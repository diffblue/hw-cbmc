/*******************************************************************\

Module: Show Formula Solver

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show Formula Solver

#include "show_formula_solver.h"

#include <util/console.h>
#include <util/format_expr.h>
#include <util/std_expr.h>

show_formula_solvert::show_formula_solvert()
  : out(consolet::out()), console(true)
{
}

void show_formula_solvert::set_to(const exprt &expr, bool value)
{
  if(console)
    out << consolet::faint;

  out << '(' << (++conjunct_counter) << ") ";

  if(console)
    out << consolet::reset;

  if(value)
    out << format(expr) << '\n';
  else
    out << format(not_exprt(expr)) << '\n';
}

exprt show_formula_solvert::handle(const exprt &expr)
{
  return expr;
}

exprt show_formula_solvert::get(const exprt &) const
{
  return nil_exprt();
}

void show_formula_solvert::push(const std::vector<exprt> &)
{
}

void show_formula_solvert::push()
{
}
