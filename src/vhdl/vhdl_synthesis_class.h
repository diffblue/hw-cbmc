/*******************************************************************\

Module: VHDL Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VHDL_SYNTHESIS_CLASS_H
#define CPROVER_VHDL_SYNTHESIS_CLASS_H

#include <util/symbol_table.h>
#include <util/std_code.h>
#include <util/message.h>

class vhdl_synthesist:public messaget
{
public:
  vhdl_synthesist(
    symbol_tablet &_symbol_table,
    const irep_idt &_module,
    message_handlert &_message_handler):
    messaget(_message_handler),
    symbol_table(_symbol_table),
    module(_module)
  {
  }
  
  bool operator()();

protected:
  symbol_tablet &symbol_table;
  const irep_idt &module;

  unsigned property_counter;
  
  void synth_module(const irept &);
  void synth_process(const exprt &);
  void synth_code(const codet &);
  
  std::vector<exprt> trans, init, invar;
};

#endif

