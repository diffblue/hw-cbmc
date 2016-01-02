/*******************************************************************\

Module: Extracting Counterexamples

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>

#include "instantiate_word_level.h"
#include "trans_trace_word_level.h"

/*******************************************************************\

Function: compute_trans_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void compute_trans_trace(
  const decision_proceduret &decision_procedure,
  unsigned no_timeframes,
  const namespacet &ns,
  const irep_idt &module,
  trans_tracet &dest)
{
  // look up the module symbol
  {
    const symbolt &symbol=ns.lookup(module);
    dest.mode=id2string(symbol.mode);
  }

  dest.states.resize(no_timeframes);

  for(unsigned t=0; t<no_timeframes; t++)
  {
    const symbol_tablet &symbol_table=ns.get_symbol_table();

    assert(t<dest.states.size());
    trans_tracet::statet &state=dest.states[t];
    
    forall_symbol_module_map(it, symbol_table.symbol_module_map, module)
    {
      const symbolt &symbol=ns.lookup(it->second);

      if(!symbol.is_type &&
         !symbol.is_property &&
         symbol.type.id()!=ID_module &&
         symbol.type.id()!=ID_module_instance)
      {
        exprt indexed_symbol_expr(ID_symbol, symbol.type);

        indexed_symbol_expr.set(ID_identifier,
          timeframe_identifier(t, symbol.name));

        exprt value_expr=decision_procedure.get(indexed_symbol_expr);
        if(value_expr==indexed_symbol_expr)
          value_expr=nil_exprt();

        trans_tracet::statet::assignmentt assignment;
        assignment.rhs.swap(value_expr);
        assignment.lhs=symbol.symbol_expr();
      
        state.assignments.push_back(assignment);
      }
    }
  }
}

/*******************************************************************\

Function: compute_trans_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void compute_trans_trace(
  const bvt &prop_bv,
  const class prop_convt &solver,
  unsigned no_timeframes,
  const namespacet &ns,
  const irep_idt &module,
  trans_tracet &dest)  
{
  compute_trans_trace(
    solver,
    no_timeframes,
    ns,
    module,
    dest);
    
  // check the properties that got violated

  for(unsigned t=0; t<no_timeframes; t++)
  {
    assert(t<prop_bv.size());
    tvt result=solver.l_get(prop_bv[t]);
    dest.states[t].property_failed=result.is_false();
  }
}

