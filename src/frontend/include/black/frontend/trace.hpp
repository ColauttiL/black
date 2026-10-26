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

#ifndef BLACK_FRONTEND_T_HPP
#define BLACK_FRONTEND_T_HPP

#include <black/support/tribool.hpp>

#include <optional>
#include <istream>
#include <string>
#include <map>
//#include <variant>

namespace black::frontend 
{
  // using state_t = std::map<std::string, black::tribool>;

  // struct trace_t {
  //   std::optional<std::string> result;
  //   size_t loop = 0;
  //   std::vector<state_t> states;
  //   std::optional<formula> muc;
  // };

  struct check_lookup {
    formula f;
    size_t t;

    friend bool operator==(check_lookup const&, check_lookup const&) = default;
  };
  } namespace std {

    template<>
    struct hash<black::frontend::check_lookup> {
      size_t operator()(black::frontend::check_lookup l) const {
        using namespace black_internal;
        using namespace black;
        size_t h1 = std::hash<formula>{}(l.f);
        size_t h2 = std::hash<size_t>{}(l.t);

        return hash_combine(h1, h2);
      }
    };

  } namespace black::frontend {

    
}


#endif