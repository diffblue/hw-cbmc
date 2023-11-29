/*******************************************************************\

Module: Extracting Counterexamples

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/symbol_table.h>
#include <util/arith_tools.h>

#include "instantiate_word_level.h"
#include "trans_trace_word_level.h"

/*******************************************************************\

Function: compute_trans_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

trans_tracet compute_trans_trace(
  const decision_proceduret &decision_procedure,
  std::size_t no_timeframes,
  const namespacet &ns,
  const irep_idt &module)
{
  trans_tracet dest;

  // look up the module symbol
  {
    const symbolt &symbol=ns.lookup(module);
    dest.mode=id2string(symbol.mode);
  }

  dest.states.resize(no_timeframes);

  for(std::size_t t = 0; t < no_timeframes; t++)
  {
    const symbol_tablet &symbol_table=ns.get_symbol_table();

    DATA_INVARIANT(t < dest.states.size(), "t is in range");
    trans_tracet::statet &state=dest.states[t];
    
    for(auto it=symbol_table.symbol_module_map.lower_bound(module);
        it!=symbol_table.symbol_module_map.upper_bound(module);
        it++)
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

  return dest;
}

/*******************************************************************\

Function: compute_trans_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

trans_tracet compute_trans_trace(
  const exprt::operandst &prop_handles,
  const decision_proceduret &solver,
  std::size_t no_timeframes,
  const namespacet &ns,
  const irep_idt &module)
{
  trans_tracet trace = compute_trans_trace(solver, no_timeframes, ns, module);

  // check the properties that got violated

  for(std::size_t t = 0; t < no_timeframes; t++)
  {
    DATA_INVARIANT(
      t < prop_handles.size(),
      "There must be exactly one prop_handles element per time frame");
    auto result = solver.get(prop_handles[t]);
    trace.states[t].property_failed = result.is_false();
  }

  return trace;
}
