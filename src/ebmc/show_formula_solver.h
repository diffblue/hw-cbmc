/*******************************************************************\

Module: Show Formula Solver

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show Formula Solver

#ifndef EBMC_SHOW_FORMULA_SOLVER_H
#define EBMC_SHOW_FORMULA_SOLVER_H

#include <solvers/stack_decision_procedure.h>

class show_formula_solvert : public stack_decision_proceduret
{
public:
  // console
  show_formula_solvert();

  // file
  explicit show_formula_solvert(std::ostream &_out) : out(_out), console(false)
  {
  }

  void set_to(const exprt &, bool value) override;
  exprt handle(const exprt &) override;
  exprt get(const exprt &) const override;
  void print_assignment(std::ostream &) const override
  {
  }

  std::string decision_procedure_text() const override
  {
    return "show-formula solver";
  }

  std::size_t get_number_of_solver_calls() const override
  {
    return 0;
  }

  ~show_formula_solvert() = default;

  void push(const std::vector<exprt> &) override;
  void push() override;

  void pop() override
  {
  }

protected:
  resultt dec_solve(const exprt &) override
  {
    return resultt::D_ERROR;
  }

  std::ostream &out;
  bool console;
  std::size_t conjunct_counter = 0;
};

#endif // EBMC_SHOW_FORMULA_SOLVER_H
