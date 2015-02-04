/*******************************************************************\

Module: Language Registration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <langapi/mode.h>

#include <smvlang/smv_language.h>

#ifdef HAVE_VERILOG
#include <verilog/verilog_language.h>
#endif

#ifdef HAVE_VHDL
#include <vhdl/vhdl_language.h>
#endif

#ifdef HAVE_NETLIST
#include <netlist/netlist_language.h>
#endif

#include "ebmc_parse_options.h"

/*******************************************************************\

Function: ebmc_parse_optionst::register_languages

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ebmc_parse_optionst::register_languages()
{
  register_language(new_smv_language);

  #ifdef HAVE_NETLIST
  register_language(new_netlist_language);
  #endif
  
  #ifdef HAVE_VERILOG
  register_language(new_verilog_language);
  #endif

  #ifdef HAVE_VHDL
  register_language(new_vhdl_language);
  #endif
}

