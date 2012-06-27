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

void diatest(bool efficient, unsigned no_states, unsigned state_bits)
{
  std::cout << (efficient?"Efficient:":"Simple:") << std::endl;

  dimacs_cnft solver;

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

  std::cout << "Variables: " << solver.no_variables() << std::endl;
  std::cout << "Clauses:   " << solver.no_clauses() << std::endl;

  std::cout << std::endl;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void diatest(unsigned bound, unsigned state_bits)
{
  unsigned no_states=bound+1;

  std::cout << "Testing recurrence diameter computation:" << std::endl;
  std::cout << "States: " << no_states << std::endl;
  std::cout << "State bits: " << state_bits << std::endl;
  diatest(0, no_states, state_bits);
  diatest(1, no_states, state_bits);
}
