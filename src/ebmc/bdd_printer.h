/*******************************************************************\

Module: BDD Function Printer

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// BDD Function Printer

#ifndef CPROVER_EBMC_BDD_PRINTER_H
#define CPROVER_EBMC_BDD_PRINTER_H

#include <iosfwd>

class mini_bddt;

/// Output the Boolean function represented by the given BDD
/// in disjunctive normal form (one cube per line) to \p out.
void print_bdd(const mini_bddt &, std::ostream &out);

#endif // CPROVER_EBMC_BDD_PRINTER_H
