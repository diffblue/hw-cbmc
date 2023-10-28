/*******************************************************************\

Module: DIMACS CNF Writer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DIMACS_WRITER_H
#define CPROVER_DIMACS_WRITER_H

#include <solvers/sat/dimacs_cnf.h>

class dimacs_cnf_writert:public dimacs_cnft
{
public:
  dimacs_cnf_writert(std::ostream &_out, message_handlert &_message_handler)
    : dimacs_cnft(_message_handler), out(_out)
  {
  }

  virtual ~dimacs_cnf_writert();

  std::string solver_text() const override
  {
    return "DIMACS CNF Writer";
  }

protected:
  std::ostream &out;
};

#endif // CPROVER_DIMACS_WRITER_H
