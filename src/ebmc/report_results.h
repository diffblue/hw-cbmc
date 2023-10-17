/*******************************************************************\

Module: Result Reporting

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Result Reporting

#ifndef EBMC_REPORT_RESULTS
#define EBMC_REPORT_RESULTS

#include "ebmc_properties.h"

class message_handlert;
class namespacet;

void report_results(
  const cmdlinet &,
  const ebmc_propertiest &,
  const namespacet &,
  message_handlert &);

#endif // EBMC_REPORT_RESULTS
