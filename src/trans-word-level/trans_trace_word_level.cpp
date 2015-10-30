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

Function: compute_trans_trace_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void compute_trans_trace_properties(
  const std::list<std::string> &prop_names,
  const std::list<bvt> &prop_bv,
  const propt &solver,
  unsigned no_timeframes,
  trans_tracet &dest)  
{
  // check the properties that got violated
  
  assert(prop_names.size()==prop_bv.size());

  for(std::list<bvt>::const_iterator
      p_it=prop_bv.begin();
      p_it!=prop_bv.end();
      p_it++)
  {
    dest.properties.push_back(trans_tracet::propertyt());

    const bvt &bv=*p_it;
    assert(bv.size()==no_timeframes);
    
    bool saw_unknown=false,
         saw_failure=false;
  
    for(unsigned t=0; t<no_timeframes; t++)
    {
      tvt result=solver.l_get(bv[t]);

      if(result.is_unknown())
      {
        saw_unknown=true;
      }
      else if(result.is_false())
      {
        dest.properties.back().failing_timeframe=t;
        saw_failure=true;
        break; // next property
      }
    }

    if(saw_failure)
      dest.properties.back().status=tvt(false);
    else if(saw_unknown)
      dest.properties.back().status=tvt::unknown();
    else
      dest.properties.back().status=tvt(true);
  }

  // put property names in
  trans_tracet::propertiest::iterator p_it=
    dest.properties.begin();
  for(std::list<std::string>::const_iterator
      n_it=prop_names.begin();
      n_it!=prop_names.end();
      n_it++, p_it++)
  {
    assert(p_it!=dest.properties.end());
    p_it->name=*n_it;
  }

}

/*******************************************************************\

Function: compute_trans_trace_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void compute_trans_trace_properties(
  const std::list<std::string> &prop_names,
  const std::list<bvt> &prop_bv,
  const prop_convt &solver,
  unsigned no_timeframes,
  trans_tracet &dest)  
{
  // check the properties that got violated

  assert(prop_names.size()==prop_bv.size());

  for(std::list<bvt>::const_iterator
      p_it=prop_bv.begin();
      p_it!=prop_bv.end();
      p_it++)
  {
    dest.properties.push_back(trans_tracet::propertyt());

    const bvt &bv=*p_it;
    assert(bv.size()==no_timeframes);
    
    bool saw_unknown=false,
         saw_failure=false;
  
    for(unsigned t=0; t<no_timeframes; t++)
    {
      tvt result=solver.l_get(bv[t]);

      if(result.is_unknown())
      {
        saw_unknown=true;
      }
      else if(result.is_false())
      {
        dest.properties.back().failing_timeframe=t;
        saw_failure=true;
        break; // next property
      }
    }

    if(saw_failure)
      dest.properties.back().status=tvt(false);
    else if(saw_unknown)
      dest.properties.back().status=tvt::unknown();
    else
      dest.properties.back().status=tvt(true);
  }

  // put names in
  trans_tracet::propertiest::iterator p_it=
    dest.properties.begin();
  for(std::list<std::string>::const_iterator
      n_it=prop_names.begin();
      n_it!=prop_names.end();
      n_it++, p_it++)
  {
    assert(p_it!=dest.properties.end());
    p_it->name=*n_it;
  }

}

/*******************************************************************\

Function: compute_trans_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void compute_trans_trace(
  const std::list<std::string> &prop_names,
  const std::list<bvt> &prop_bv,
  const class prop_convt &solver,
  unsigned no_timeframes,
  const namespacet &ns,
  const irep_idt &module,
  trans_tracet &dest)  
{
  assert(prop_names.size()==prop_bv.size());

  compute_trans_trace(
    solver,
    no_timeframes,
    ns,
    module,
    dest);
    
  // check the properties that got violated
  
  compute_trans_trace_properties(
    prop_names,
    prop_bv,
    solver,
    no_timeframes,
    dest);
}

