/*******************************************************************\

Module: Show Properties

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_SHOW_PROPERTIES_H
#define CPROVER_EBMC_SHOW_PROPERTIES_H

#include <string>

class ebmc_propertiest;
class ui_message_handlert;

void show_properties(const ebmc_propertiest &, ui_message_handlert &);
void json_properties(const ebmc_propertiest &, const std::string &file_name);

#endif
