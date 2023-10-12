/*******************************************************************\

Module: Diameter Test

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DIATEST_H
#define CPROVER_DIATEST_H

class message_handlert;

void diatest(unsigned bound, unsigned state_bits, message_handlert &);

#endif // CPROVER_DIATEST_H
