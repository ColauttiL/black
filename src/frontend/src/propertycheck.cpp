//
// BLACK - Bounded Ltl sAtisfiability ChecKer
//
// (C) 2021 Nicola Gigante
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

#include <black/frontend/tracecheck.hpp>
#include <black/frontend/io.hpp>
#include <black/frontend/support.hpp>
#include <black/frontend/trace.hpp>

#include <black/logic/logic.hpp>
#include <black/logic/parser.hpp>
#include <black/logic/prettyprint.hpp>
#include <black/logic/past_remover.hpp>
#include <black/solver/solver.hpp>
#include <black/support/tribool.hpp>

#include <iostream>
#include <sstream>
#include <algorithm>
#include <optional>
#include <variant>
#include <typeinfo>

#include <nlohmann/json.hpp>

using json = nlohmann::json;

namespace black::frontend 
{

  using ValueType = std::variant<black::tribool, int, double>;
  using state_t1 = std::map<std::string, ValueType>;
  
  struct trace_t1 {
    std::optional<std::string> result;
    size_t loop = 0;
    std::vector<state_t1> states;
    std::optional<formula> muc;
  };

  static bool check(trace_t1, formula, size_t);

  bool is_pure_past(formula f, int i) { 
    
    //bool result = f.match(
    return f.match(
      [](boolean) { return true; },
      [&](proposition) { return true; },
      [&](atom) -> bool { 
        command_line_error("atoms are not supported by the LIA and the LRA quantifier-free theories");
        quit(status_code::command_line_error); },
      [&](quantifier) -> bool { 
        command_line_error("the --safety and --cosafety options do not accept quantifiers)");
        quit(status_code::command_line_error); },
      [&](equality) { return true; },
      [&](comparison) -> bool { return true; },
      [&](tomorrow, formula) { return false; },
      [&](w_tomorrow, formula) { return false; },
      [&](yesterday, formula op) { return is_pure_past(op, i+1); },
      [&](w_yesterday, formula op) { return is_pure_past(op, i+1); },
      [&](until) { return false; },
      [&](w_until) { return false; },
      [&](since, formula l, formula r) { return is_pure_past(l, i+1) && is_pure_past(r, i+1); },
      [&](negation, formula op) { return is_pure_past(op, i); }, // { return is_pure_past(op, i+1); },
      [&](conjunction, formula l, formula r) { return is_pure_past(l, i+1) && is_pure_past(r, i+1); },
      [&](disjunction, formula l, formula r) { return is_pure_past(l, i+1) && is_pure_past(r, i+1); },
      [&](implication, formula l, formula r) { return is_pure_past(l, i+1) && is_pure_past(r, i+1); },
      [&](iff, formula l, formula r) { return is_pure_past(l, i+1) && is_pure_past(r, i+1); },
      [&](eventually, formula op) { return (i==0 && is_pure_past(op, i+1)); }, 
      [&](always, formula op) { return i==0 && is_pure_past(op, i+1); },
      [&](release, formula, formula) { return false; },
      [&](s_release, formula, formula) { return false; },
      [&](once, formula op) { return is_pure_past(op, i+1); },
      [&](historically, formula op) { return is_pure_past(op, i+1); },
      [&](triggered, formula l, formula r) { return is_pure_past(l, i+1) && is_pure_past(r, i+1); }
    );
  }


  static 
  trace_t1 parse_trace(
    alphabet &sigma, 
    std::optional<std::string> const&tracepath, std::istream &file
  ) {
    std::string path = tracepath ? *tracepath : "<stdin>";
    json j;
    try {
      j = json::parse(file);

      trace_t1 trace;
      if(!j["result"].is_null())
        trace.result = j["result"];

      json jmuc = j["muc"];
      if(!jmuc.is_null()) {
        std::string smuc = jmuc.get<std::string>();
        trace.muc =
          black::parse_formula(
            sigma, smuc, [&](auto error) {
              io::fatal(
                status_code::syntax_error, "{}: malformed 'muc' field: {}", 
                path, error
              );
            }
          );
        black_assert(trace.muc.has_value());
      }

      json model = j["model"];
      if(model.is_null())
        return trace;

      if(cli::finite)
        io::println("the --finite option is implied when solving |LTLfMT| formulas, since the infinite-trace semantics is not supported for such formulas.");
        
      trace.loop = model["size"];

      if(!(model["loop"] == 0)){
        if(!(model["loop"].is_null())){
          io::fatal(
            status_code::syntax_error, 
            "expected a finite model, but a \"loop\" field is present"
          );
        }
      }

      if(model["states"].size() == 0)
        io::fatal(status_code::syntax_error, "{}: empty model", path);

      for(json jstate : model["states"]) {
        std::map<std::string, ValueType> state;

        for(auto it = jstate.begin(); it != jstate.end(); ++it) {
          ValueType value = black::tribool::undef;
          
          
          try{
            if(it.value().get<std::string>() == "undef")
              value = black::tribool::undef;
            else if(it.value().get<std::string>() == "true"){
              black::tribool bool__val = true;
              value = bool__val;
            }else if(it.value().get<std::string>() == "false"){
              black::tribool bool__val = false;
              value = bool__val;
            }
          } catch(std::exception& e) {
            try{ 
              int it_value = it.value().get<int>();
              if(cli::default_sort == "Real")
                io::fatal(
                  status_code::syntax_error, 
                  "{}: found integer value in real domain",
                  path
                );

              value = it_value;
            }catch(std::exception& e) {
              try{
                double it_value = it.value().get<double>();  
                
                if(cli::default_sort == "Int")
                  io::fatal(
                    status_code::syntax_error, 
                    "{}: found real value in Int domain",
                    path
                  );
                value = it_value;

              } catch(std::exception& e) {
                io::fatal(
                status_code::syntax_error, 
                "{}: invalid proposition value",
                path
              );
              }
            }
          }
          
          state.insert({it.key(), value});
        }
        //trace.states.push_back(state);
        trace.states.insert(trace.states.begin(),state);
      }

      if(model["size"] != trace.states.size()) {
        io::fatal(
          status_code::syntax_error, 
          "{}: \"size\" field and effective model size disagree",
          path
        );
      }

      if(trace.loop > trace.states.size()) {
        io::fatal(
          status_code::syntax_error, 
          "{}: \"loop\" field greater than model size",
          path
        );
      }
      
      return trace;

    } catch (json::exception& ex) {
      io::fatal(status_code::syntax_error, "{}:{}", path, ex.what());
    }
  }

  static
  std::optional<state_t1> state_at(trace_t1 trace, size_t t) {
    // if(t < trace.loop)
    //   return trace.states[t];
    
    // size_t period = trace.states.size() - trace.loop;

    // if(period)
    //   return trace.states[((t - trace.loop) % period) + trace.loop];
    
    // black_assert(t >= trace.states.size());
    if(t >= trace.states.size())
      return {};

    return trace.states[t];
  }

  
  static
  ValueType check_eq_comp_proposition(trace_t1 trace, std::string p, size_t t) {
    std::optional<state_t1> state = state_at(trace, t);
   
    // all the states at the end of a non-looping model are
    // full of don't cares so we return true (we may choose false as well)
    if(!state.has_value()){
      return true;
    }
      
    auto it = state->find(p);

    if(it == state->end()){   
      return true;
    }

    ValueType value = it->second;  
    try{
      if(get<black::tribool>(value)){
        io::fatal(
          status_code::syntax_error, 
          "unable to find a numerical value of the requested variable"
        ); 
      }

    }catch(std::exception& e) {
      try{
        if(get<int>(value)){
          int int_value = get<int>(value);
          return int_value;
        }
      } catch(std::exception& e){
        try{
          if(get<double>(value)){
            double double_value = get<double>(value);
            return double_value;
          }
        } catch(std::exception& e){
          io::fatal(
            status_code::syntax_error, 
            "invalid proposition value"
          );
        }

      }
    }
    io::fatal(
      status_code::syntax_error, 
      "unrecognized proposition value"
    );

  }


  static
  bool check_proposition(trace_t1 trace, proposition a, size_t t) {
    black_assert(a.name().to<std::string>().has_value());
    std::string p = *a.name().to<std::string>();

    std::optional<state_t1> state = state_at(trace, t);
   
    // all the states at the end of a non-looping model are
    // full of don't cares so we return true (we may choose false as well)
    if(!state.has_value()){
      return true;
    }
      
    auto it = state->find(p);

    if(it == state->end()){
      return true;
    }

    ValueType value = it->second;  // si suppone che le  var a se stanti siano bool

    try{
      black::tribool trib_val = get<black::tribool>(value);
      
      
      if(trib_val == black::tribool::undef){
        return true;
      }
      else if(trib_val == true){
        return true;
      }
      else if(trib_val == false){
        return false;
      } 
    

    }catch(std::exception& e) {
      io::fatal(
        status_code::syntax_error, 
        "invalid proposition value (numeric)"
      );
      // try{
      //   if(get<int>(value))
      //     ...
      // } catch(std::exception& e){
      //     ...
      //   try{
      //     if(get<double>(value))
      //       ...
      //   } catch(std::exception& e){
      //     io::fatal(
      //       status_code::syntax_error, 
      //       "invalid proposition value"
      //     );
      //   }
      // }
    }
    return false;
  }
   

  static
  std::optional<size_t>
  find_one_reverse(trace_t1 trace, formula f, size_t begin, size_t end) { // controlla in (l S r) se r è valso da oggi (begin) in prima (end=0) 
    for(ssize_t i = (ssize_t)begin; i >= (ssize_t)end; --i) {
      if(check(trace, f, (size_t)i))
        return i; // restituisce la posizione in cui trova r
    }
    return {};
  }
  
  static
  bool check_for_all(trace_t1 trace, formula f, size_t begin, size_t end) { // controlla se dall'istante della funzione precedente è sempre valso l
    for(size_t i = begin; i < end; ++i) {
      if(!check(trace, f, i))
        return false;
    }
    return true;
  }

  static
  bool check_since(trace_t1 trace, since s, size_t t) {
    formula l = s.left();
    formula r = s.right();
    
    // search for 'r'
    std::optional<size_t> rindex = find_one_reverse(trace, r, t, 0);

    if(!rindex.has_value())
      return false; // we didn't find 'r', the formula is false

    // check 'l' in all positions until 'r'
    return check_for_all(trace, l, *rindex + 1, t + 1);
  }

  static int check(trace_t1 trace, formula f) {

    size_t initial_state = 0;
    if(cli::initial_state)
      initial_state = *cli::initial_state;

    bool result = check(trace, f, initial_state);
    if(result)
      io::println("TRUE");
    else {
      io::println("FALSE");
      quit(status_code::failed_check);
    }
    
    return 0;
  }


  auto check_term_value(trace_t1 trace, term term, size_t t){
    auto value = term.match(
      [&](variable, identifier id){
        if (id.to<std::string>()){
          std::string var_id = id.to<std::string>().value();
          ValueType value = check_eq_comp_proposition(trace, var_id, t);
          if (cli::default_sort == "Int" || cli::default_sort == "int"){
            int int_value = get<int>(value);
            return int_value;
          } else if(cli::default_sort == "Real" || cli::default_sort == "real"){
            int double_value = get<double>(value);
            return double_value;
          } else { 
            io::fatal(
              status_code::syntax_error, "found an unexpected sort"
            );
          }
        }
        else { 
          io::fatal(
            status_code::syntax_error, "could not find the variable identifier"
          );
        }
      },
      [&](constant, number n){
        auto res = n.match(
          [&](integer i){
            int int_value = i.value();
            return int_value;
          },
          [&](real r){
            double double_value = r.value();
            return double_value;
          }
        );
        return res;
      }
    );

    return value;
    
  }


  bool check_equality(trace_t1 trace, equality e, size_t t){
  
    bool result = e.match(
      [&](equal, auto terms) {  
        int terms_size = terms.size();
        auto first_value = 0;

        for(int i = 0; i< terms_size; i++ ){
          auto value = check_term_value(trace, terms[i], t);

          if(i == 0){
            first_value = value; // if it's the first cycle, initialize the variable with the first number
          } else {
            if (first_value != value ) {
              return false;
            }
          }
        }
        return true;
      },
      [&](distinct, auto terms) {  
        int terms_size = terms.size();
        auto first_value = 0;

        for(int i = 0; i< terms_size; i++ ){
          auto value = check_term_value(trace, terms[i], t);

          if(i == 0){
            first_value = value; // if it's the first cycle, initialize the variable with the first number
          } else {
            if (first_value != value ) {
              return true;
            }
          }
        }
        return false;
      }
    );
    return result;
  }

  
  bool check_comparison(trace_t1 trace, comparison c, size_t t){
    return c.match(
      [&](less_than, term l, term r) { 
        auto l_value = check_term_value(trace, l, t);
        auto r_value = check_term_value(trace, r, t);
        return l_value < r_value; 
      },
      [&](less_than_equal, term l, term r) {
        auto l_value = check_term_value(trace, l, t);
        auto r_value = check_term_value(trace, r, t);
        return l_value <= r_value; 
      },
      [&](greater_than, term l, term r) {
        auto l_value = check_term_value(trace, l, t);
        auto r_value = check_term_value(trace, r, t);
        return l_value > r_value; 
      },
      [&](greater_than_equal, term l, term r) {
        auto l_value = check_term_value(trace, l, t);
        auto r_value = check_term_value(trace, r, t);
        return l_value >= r_value;
      }
     );
  }

  static bool check(trace_t1 trace, formula f, size_t t) 
  {
    static std::unordered_map<check_lookup, bool> memo;
    if(auto it = memo.find({f, t}); it != memo.end())
      return it->second;

    bool result = f.match(
      [](boolean b) {
        return b.value();
      },
      [&](proposition a) {
        return check_proposition(trace, a, t);
      },
      [&](equality e) -> bool { return check_equality(trace, e, t); }, 
      [&](comparison c) -> bool { return check_comparison(trace, c, t); }, 
      [&](yesterday, formula op) {
        return t > 0 && check(trace, op, t - 1); // +1 because the trace is reversed
      },
      [&](w_yesterday, formula op) {
        return t == 0 || check(trace, op, t + 1);
      },
      // [&](until u) {
      //   return check_until(trace, u, t);
      // },
      [&](since s) {
        return check_since(trace, s, t);
      },
      [&](negation, formula op) {
        return !check(trace, op, t);
      },
      [&](conjunction, formula l, formula r) {
        return check(trace, l, t) && check(trace, r, t);
      },
      [&](disjunction, formula l, formula r) {
        return check(trace, l, t) || check(trace, r, t);
      },
      [&](implication, formula l, formula r) {
        return !check(trace, l, t) || check(trace, r, t);
      },
      [&](iff, formula l, formula r) {
        return check(trace, l, t) == check(trace, r, t);
      },
      [&](eventually, formula op) {
        return check(trace, U(op.sigma()->top(), op), t);
      },
      [&](always, formula op) {
        return check(trace, !F(!op), t);
      },
      [&](once, formula op) {
        return check(trace, S(op.sigma()->top(), op), t);
      },
      [&](historically, formula op) {
        return check(trace, !O(!op), t);
      },
      [&](triggered, formula l, formula r) {
        return check(trace, !S(!l, !r), t);
      }
    );

    if(cli::verbose)
      io::println("{} at t = {} is {}", to_string(f), t, result);

    memo.insert({{f,t}, result});

    return result;
  }


  static
  int property_check(
    std::optional<std::string> const&path, //formula filename
    std::istream &file, // formula string
    std::optional<std::string> const&tracepath, //tracefile
    std::istream &tracefile // trace string
  ) {
    black::alphabet sigma;
    std::optional<formula> f = black::parse_formula(sigma, file, formula_syntax_error_handler(path));
    
    black_assert(f.has_value());
    trace_t1 trace = parse_trace(sigma, tracepath, tracefile);
    
    if (f.has_value()) {
      black_internal::logic::formula fi = *f;
      // if (cli::check_safety)
      //   printf("SAFETY\n");
      // if (cli::check_cosafety)
      //   printf("COSAFETY\n");
      
      bool b = is_pure_past(fi, 0);

      if (!b){
        command_line_error("the formula is not of the form G(pure_past_formula) or F(pure_past_formula)");
        quit(status_code::command_line_error);
      } 
    }  
    
    if(cli::expected_result) {
      if(trace.result != *cli::expected_result) {
        io::println("MISMATCH");
        quit(status_code::failed_check);
      }

      if(trace.result == *cli::expected_result)
        io::println("MATCH");
    }

    if(trace.muc.has_value()) {
      scope xi{sigma};
      xi.set_default_sort(sigma.named_sort("default"));
      
      black::solver slv;
      if(slv.solve(xi, *trace.muc, cli::finite) != false) {
        io::println("SAT CORE");
        quit(status_code::failed_check);
      }
    }

    if(trace.states.size() == 0){
      quit(status_code::success);
    }
    return check(trace, *f);
  } 


  int property_check() {
    if(cli::check_safety && cli::check_cosafety){
      command_line_error("please choose only one between the --safety and --cosafety options");
      quit(status_code::command_line_error);
    }

    if(!cli::filename && !cli::formula) {
      command_line_error("please specify a filename or the --formula option");
      quit(status_code::command_line_error);
    }

    if(cli::filename && cli::formula) {
      command_line_error("please specify only either a filename or the --formula option");
      quit(status_code::command_line_error);
    }

    if(cli::filename == "-" && cli::trace == "-") {
      command_line_error("cannot read from stdin both the formula file and the trace file");
      quit(status_code::command_line_error);
    }

    if(cli::formula) {
      std::istringstream str{*cli::formula};

      if(cli::trace == "-")
        return property_check(std::nullopt, str, std::nullopt, std::cin);

      std::ifstream tracefile = open_file(cli::trace);
      return property_check(std::nullopt, str, cli::trace, tracefile);
    }

    if(cli::filename == "-") {
      std::ifstream tracefile = open_file(cli::trace);
      return property_check(std::nullopt, std::cin, cli::trace, tracefile);
    }

    if(cli::trace == "-") {
      std::ifstream file = open_file(*cli::filename);
      return property_check(cli::filename, file, std::nullopt, std::cin);
    }

    std::ifstream file = open_file(*cli::filename);
    std::ifstream tracefile = open_file(cli::trace);
    return property_check(cli::filename, file, cli::trace, tracefile);
  }

}

