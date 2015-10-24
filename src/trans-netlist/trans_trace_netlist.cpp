/*******************************************************************\

Module: Extracting Counterexamples

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ctime>
#include <cassert>
#include <string>
#include <iostream>

#include <util/xml.h>
#include <util/xml_expr.h>
#include <util/i2string.h>
#include <util/expr_util.h>
#include <util/prefix.h>
#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/pointer_offset_size.h>

#include <langapi/language_util.h>

#include "instantiate_netlist.h"
#include "trans_trace_netlist.h"

/*******************************************************************\

Function: compute_trans_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void compute_trans_trace(
  const std::list<std::string> &prop_names,
  const std::list<bvt> &prop_bv,
  const bmc_mapt &bmc_map,
  const propt &solver,
  const namespacet &ns,
  trans_tracet &dest)
{
  assert(prop_names.size()==prop_bv.size());

  dest.states.reserve(bmc_map.get_no_timeframes());
  
  for(unsigned t=0; t<bmc_map.get_no_timeframes(); t++)
  {
    dest.states.push_back(trans_tracet::statet());
    trans_tracet::statet &state=dest.states.back();
  
    for(var_mapt::mapt::const_iterator
        it=bmc_map.var_map.map.begin();
        it!=bmc_map.var_map.map.end();
        it++)
    {
      const var_mapt::vart &var=it->second;

      // we show latches, inputs, wires      
      if(!var.is_latch() && !var.is_input() && !var.is_wire())
        continue;
        
      const symbolt &symbol=ns.lookup(it->first);

      std::string value;
      value.reserve(var.bits.size());

      for(unsigned i=0; i<var.bits.size(); i++)
      {
        literalt l=bmc_map.get(t, var.bits[i]);

        char ch;

        switch(solver.l_get(l).get_value())
        {
         case tvt::TV_TRUE: ch='1'; break;
         case tvt::TV_FALSE: ch='0'; break;
         default: ch='?'; break;
        }

        value=ch+value;
      }
      
      state.assignments.push_back(trans_tracet::statet::assignmentt());

      trans_tracet::statet::assignmentt &assignment=
        state.assignments.back();

      assignment.lhs=symbol.symbol_expr();
      assignment.rhs=bitstring_to_expr(value, var.type);
      assignment.location.make_nil();
    }
  }

  // check the properties that got violated
  
  compute_trans_trace_properties(
    prop_names,
    prop_bv,
    solver,
    bmc_map.get_no_timeframes(),
    dest);
}         
          
