/*******************************************************************\

Module: SMV Keywords

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_SMVLANG_SMV_KEYWORDS_H
#define CPROVER_SMVLANG_SMV_KEYWORDS_H

#include <util/irep.h>

/// Returns true iff the given identifier is a NuSMV keyword.
bool is_smv_keyword(const irep_idt &);

#endif // CPROVER_SMVLANG_SMV_KEYWORDS_H
