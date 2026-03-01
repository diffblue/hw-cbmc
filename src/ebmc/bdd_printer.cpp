/*******************************************************************\

Module: BDD Function Printer

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// BDD Function Printer

#include "bdd_printer.h"

#include <solvers/bdd/miniBDD/miniBDD.h>

#include <ostream>
#include <string>
#include <vector>

static void print_bdd_rec(
  const mini_bddt &bdd,
  std::vector<std::string> &cube,
  std::ostream &out)
{
  if(bdd.is_false())
    return;

  if(bdd.is_true())
  {
    bool first = true;
    for(const auto &literal : cube)
    {
      if(!first)
        out << u8" \u2227 ";
      out << literal;
      first = false;
    }
    out << '\n';
    return;
  }

  const mini_bdd_mgrt &mgr = *bdd.node->mgr;
  const std::string &label = mgr.var_table[bdd.var() - 1].label;

  cube.push_back(u8"\u00ac" + label);
  print_bdd_rec(bdd.low(), cube, out);
  cube.pop_back();

  cube.push_back(label);
  print_bdd_rec(bdd.high(), cube, out);
  cube.pop_back();
}

void print_bdd(const mini_bddt &bdd, std::ostream &out)
{
  if(bdd.is_false())
    out << "false\n";
  else if(bdd.is_true())
    out << "true\n";
  else
  {
    std::vector<std::string> cube;
    print_bdd_rec(bdd, cube, out);
  }
}
