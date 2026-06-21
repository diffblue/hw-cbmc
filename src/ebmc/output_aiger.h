/*******************************************************************\

Module: Output AIGER

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_OUTPUT_AIGER_H
#define CPROVER_EBMC_OUTPUT_AIGER_H

#include <iosfwd>

class netlistt;

/// Write the given netlist in AIGER format to the given stream.
void output_aiger(const netlistt &, std::ostream &);

#endif // CPROVER_EBMC_OUTPUT_AIGER_H
