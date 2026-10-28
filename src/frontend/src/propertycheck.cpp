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

  bool is_pure_past(formula f, int i);
  bool form_check(formula f, int neg);


  bool form_check(formula f, int neg){
    return f.match(
      [&](negation, formula op) { 
        return form_check(op, !neg);
        }, 
      [&](always, formula op1){ 
        if (cli::check_safety && neg == 1){
          command_line_error("detected a formula of the form !G(...) with the --safety option. Try --cosafety");
          quit(status_code::command_line_error);
        } else if (cli::check_safety){
          return is_pure_past(op1, 0);
        } else if (cli::check_cosafety && neg == 1){
          return is_pure_past(op1, 0);
        } else { //(cli::check_cosafety && neg == 0)
          command_line_error("detected a formula of the form G(...) with the --cosafety option. Try --safety");
          quit(status_code::command_line_error);
        }
      },
      [&](eventually, formula op1){
        if (cli::check_safety && neg == 1){
          return is_pure_past(op1, 0);
        } else if (cli::check_safety){
          command_line_error("detected a formula of the form F(...) with the --safety option. Try --cosafety");
          quit(status_code::command_line_error);
        } else if (cli::check_cosafety && neg == 1){ 
          command_line_error("detected a formula of the form !F(...) with the --cosafety option. Try --safety");
          quit(status_code::command_line_error);
        } else { //(cli::check_cosafety && neg == 0)
          return is_pure_past(op1, 0);
        }
      },
      [&](otherwise) {
        return false;
      }
    );

  }

  bool is_pure_past(formula f, int i) { 
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
      [&](negation, formula op) { printf("neg \n"); return is_pure_past(op, i); }, 
      [&](conjunction, formula l, formula r) { return is_pure_past(l, i+1) && is_pure_past(r, i+1); },
      [&](disjunction, formula l, formula r) { return is_pure_past(l, i+1) && is_pure_past(r, i+1); },
      [&](implication, formula l, formula r) { return is_pure_past(l, i+1) && is_pure_past(r, i+1); },
      [&](iff, formula l, formula r) { return is_pure_past(l, i+1) && is_pure_past(r, i+1); },
      [&](eventually, formula op) { printf("event \n"); return (i==0 && is_pure_past(op, i+1)); }, 
      [&](always, formula op) { printf("alway \n"); return i==0 && is_pure_past(op, i+1); },
      [&](release, formula, formula) { return false; },
      [&](s_release, formula, formula) { return false; },
      [&](once, formula op) { return is_pure_past(op, i+1); },
      [&](historically, formula op) { return is_pure_past(op, i+1); },
      [&](triggered, formula l, formula r) { return is_pure_past(l, i+1) && is_pure_past(r, i+1); }
    );
  }

  
  static
  ValueType check_numerical_proposition(trace_t trace, std::string p, size_t t) {
    std::optional<state_t> state = state_at(trace, t);
   
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
          printf("found int value\n");
          return int_value;
        }
      } catch(std::exception& e){
          printf("try double\n");
        try{
          if(get<double>(value)){
            double double_value = get<double>(value);
            printf("found double value\n");
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

  auto check_term_value(trace_t trace, term term, size_t t){
    auto value = term.match(
      [&](variable, identifier id){
        if (id.to<std::string>()){
          std::string var_id = id.to<std::string>().value();
          ValueType value = check_numerical_proposition(trace, var_id, t);
          if (cli::default_sort == "Int" || cli::default_sort == "int"){
            int int_value = get<int>(value);
            
            //io::println("int var val: {}\n", int_value); 
            return int_value;
          } else if(cli::default_sort == "Real" || cli::default_sort == "real"){
            int double_value = get<double>(value);
            
            //io::println("real var val: {}\n", double_value); 
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
            io::println("constant int value: {}\n", int_value);
            return int_value;
          },
          [&](real r){
            double double_value = r.value();
            io::println("constant real value: {}\n", double_value);
            return double_value;
          }
        );
        return res;
      }
    );

    return value;
    
  }


  bool check_equality(trace_t trace, equality e, size_t t){
  
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

  
  bool check_comparison(trace_t trace, comparison c, size_t t){
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

  static bool check(trace_t trace, formula f, size_t t) 
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
        return t > 0 && check(trace, op, t - 1); 
      },
      [&](w_yesterday, formula op) {
        return t == 0 || check(trace, op, t - 1);
      },
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
        return check(trace, S(op.sigma()->top(), op), t);
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


  static int check(trace_t trace, formula f) {
     // size_t initial_state = 0;
    size_t final_state = trace.states.size() - 1; 
    //if(cli::initial_state)
    //   initial_state = *cli::initial_state;

    bool result = check(trace, f, final_state);
    if(result)
      io::println("TRUE");
    else {
      io::println("FALSE");
      quit(status_code::failed_check);
    }
    
    return 0;
  }


    static 
  trace_t parse_trace(
    alphabet &sigma, 
    std::optional<std::string> const&tracepath, std::istream &file
  ) {
    std::string path = tracepath ? *tracepath : "<stdin>";
    json j;
    try {
      j = json::parse(file);

      trace_t trace;
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
        io::println("the --finite option is implied when solving |LTLfMT| formulas, since the infinite-trace semantics is not supported for such formulas");
        
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
                io::println("double value: {}", it_value);
                
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
        trace.states.push_back(state);
        //trace.states.insert(trace.states.begin(),state);
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
  int property_check(
    std::optional<std::string> const&path, 
    std::istream &file,
    std::optional<std::string> const&tracepath,
    std::istream &tracefile 
  ) {
    black::alphabet sigma;
    std::optional<formula> f = black::parse_formula(sigma, file, formula_syntax_error_handler(path));
    
    black_assert(f.has_value());
    trace_t trace = parse_trace(sigma, tracepath, tracefile);
    
    if (f.has_value()) {
      black_internal::logic::formula fi = *f;
      
      bool b = form_check(fi, 0);

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



