/*******************************************************************\

Module: Word-Level SMV Output

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "output_smv_word_level.h"

#include "ebmc_properties.h"
#include "transition_system.h"

#include <ostream>

void output_smv_word_level(
  const transition_systemt &transition_system,
  const ebmc_propertiest &properties,
  std::ostream &out)
{
  out << "MODULE main\n";
}
