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

#include <nlohmann/json.hpp>

using json = nlohmann::json;

namespace black::frontend 
{
  using state_t = std::map<std::string, black::tribool>;

  struct trace_t {
    std::optional<std::string> result;
    size_t loop = 0;
    std::vector<state_t> states;
    std::optional<formula> muc;
  };

  bool is_pure_past(formula, int);

    int property_check() {
    if(cli::formula){
      std::istringstream str{*cli::formula};
      black::alphabet sigma;
      std::optional<formula> fi = black::parse_formula(sigma, str, formula_syntax_error_handler(std::nullopt));

      if (fi.has_value()) {
        black_internal::logic::formula f = *fi;
        bool b = is_pure_past(f, 0);
        if (!b){
          command_line_error("the formula is not of the form G(pure_past_formula) or F(pure_past_formula)");
          quit(status_code::command_line_error);
        } else {
          if (cli::check_safety)
            printf("SAFETY\n");
          if (cli::check_cosafety)
            printf("COSAFETY\n");
        }
               
      } else {
        printf("there is an error in the formula retrieval \n");
      }

    }
    return 1;
  }



  bool is_pure_past(formula f, int i) {
    
    //bool result = f.match(
    return f.match(
      [](boolean) { return true; },
      [&](proposition) { return true; },
      [&](atom) -> bool { return true; },
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
      [&](negation, formula op) { return is_pure_past(op, i+1); },
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

    //if(cli::verbose)
      //io::println("{} at t = {} is {}", to_string(f), t, result);

    //memo.insert({{f,t}, result});
  }

}