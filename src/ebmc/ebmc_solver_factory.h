/*******************************************************************\

Module: EBMC's Factory for Word-Level Solvers

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef EBMC_SOLVER_FACTORY_H
#define EBMC_SOLVER_FACTORY_H

#include <util/cmdline.h>
#include <util/message.h>
#include <util/namespace.h>

#include <solvers/decision_procedure.h>
#include <solvers/prop/prop.h>

#include <iosfwd>
#include <memory>

class ebmc_solvert final
{
public:
  explicit ebmc_solvert(std::unique_ptr<decision_proceduret> p)
    : decision_procedure_ptr(std::move(p))
  {
  }

  ebmc_solvert(
    std::unique_ptr<propt> p1,
    std::unique_ptr<decision_proceduret> p2)
    : prop_ptr(std::move(p1)), decision_procedure_ptr(std::move(p2))
  {
  }

  ebmc_solvert(
    std::unique_ptr<std::ofstream> p1,
    std::unique_ptr<decision_proceduret> p2)
    : ofstream_ptr(std::move(p1)), decision_procedure_ptr(std::move(p2))
  {
  }

  decision_proceduret &decision_procedure() const
  {
    PRECONDITION(decision_procedure_ptr);
    return *decision_procedure_ptr;
  }

  // the objects are deleted in the opposite order they appear below
  std::unique_ptr<std::ofstream> ofstream_ptr;
  std::unique_ptr<propt> prop_ptr;
  std::unique_ptr<decision_proceduret> decision_procedure_ptr;
};

using ebmc_solver_factoryt =
  std::function<ebmc_solvert(const namespacet &, message_handlert &)>;

ebmc_solver_factoryt ebmc_solver_factory(const cmdlinet &);

#endif // EBMC_SOLVER_FACTORY_H
