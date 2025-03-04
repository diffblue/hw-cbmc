/*******************************************************************\

Module: Word-Level SMV Output

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef EBMC_OUTPUT_SMV_WORD_LEVEL_H
#define EBMC_OUTPUT_SMV_WORD_LEVEL_H

#include <iosfwd>

class ebmc_propertiest;
class transition_systemt;

/// outputs word-level SMV
void output_smv_word_level(
  const transition_systemt &,
  const ebmc_propertiest &,
  std::ostream &);

#endif // EBMC_OUTPUT_SMV_WORD_LEVEL_H
