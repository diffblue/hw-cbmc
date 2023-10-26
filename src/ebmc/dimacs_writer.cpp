/*******************************************************************\

Module: DIMACS CNF Writer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "dimacs_writer.h"

dimacs_cnf_writert::~dimacs_cnf_writert()
{
  log.statistics() << no_variables() << " variables and "
                   << no_clauses() << " clauses"
                   << messaget::eom;

  write_dimacs_cnf(out);
}
