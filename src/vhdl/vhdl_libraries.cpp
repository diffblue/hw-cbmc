/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "vhdl_libraries.h"
#include "vhdl_language.h"

const char vhdl_library_standard[]=
#include "library_standard.inc"
;

/*******************************************************************\

Function: load_vhdl_library

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void load_vhdl_library(
  const irep_idt &name,
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  const char *library_text;

  if(name=="standard")
  {
    library_text=vhdl_library_standard;
  }
  else
  {
    messaget message(message_handler);
    message.error() << "Library `" << name << "' not found"
                    << messaget::eom;
    return;
  }

  std::stringstream in(library_text);  
  
  vhdl_languaget vhdl_language;
  vhdl_language.parse(in, "<builtin-library>", message_handler);
  vhdl_language.typecheck(
    symbol_table, "vhdl::" + id2string(name), message_handler);
}
