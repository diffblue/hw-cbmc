/*******************************************************************\

Module: Result Reporting

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Result Reporting

#ifndef EBMC_REPORT_RESULTS
#define EBMC_REPORT_RESULTS

#include "property_checker.h"

class message_handlert;
class namespacet;

void report_results(
  const cmdlinet &,
  bool show_proof_via,
  const property_checker_resultt &,
  const namespacet &,
  message_handlert &);

#endif // EBMC_REPORT_RESULTS
