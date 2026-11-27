/*******************************************************************\

Module: Output AIGER

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_OUTPUT_AIGER_H
#define CPROVER_EBMC_OUTPUT_AIGER_H

#include <string>

class ebmc_propertiest;
class netlistt;

/// Write the netlist and its active properties in AIGER format.
/// Reject unsupported properties before opening the output file.
void output_aiger(
  const netlistt &,
  const ebmc_propertiest &,
  const std::string &filename);

#endif // CPROVER_EBMC_OUTPUT_AIGER_H
