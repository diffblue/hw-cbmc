/*******************************************************************\

Module: Diameter Test

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <solvers/sat/dimacs_cnf.h>

#include "diameter.h"

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void diatest(bool efficient, unsigned no_states, unsigned state_bits,
             message_handlert &message_handler) {
  std::cout << (efficient?"Efficient:":"Simple:") << '\n';

  dimacs_cnft solver{message_handler};

  std::vector<bvt> states;

  states.resize(no_states);

  for(unsigned s=0; s<no_states; s++)
  {
    states[s].resize(state_bits);

    for(unsigned i=0; i<state_bits; i++)
      states[s][i]=solver.new_variable();
  }

  literalt diameter;

  if(efficient)
    diameter=efficient_diameter(solver, states);
  else
    diameter=simple_diameter(solver, states);

  std::cout << "Variables: " << solver.no_variables() << '\n';
  std::cout << "Clauses:   " << solver.no_clauses() << '\n';

  std::cout << '\n';
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void diatest(unsigned bound, unsigned state_bits,
             message_handlert &message_handler) {
  unsigned no_states=bound+1;

  std::cout << "Testing recurrence diameter computation:" << '\n';
  std::cout << "States: " << no_states << '\n';
  std::cout << "State bits: " << state_bits << '\n';
  diatest(0, no_states, state_bits, message_handler);
  diatest(1, no_states, state_bits, message_handler);
}
