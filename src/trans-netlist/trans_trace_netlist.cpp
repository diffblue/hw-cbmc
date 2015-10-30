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

Function: bitstring_to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt bitstring_to_expr(const std::string &src, const typet &type)
{
  exprt value_expr;
  value_expr.make_nil();

  if(type.id()==ID_range ||
     type.id()==ID_unsignedbv ||
     type.id()==ID_signedbv)
  {
    value_expr=constant_exprt(type);

    if(type.id()==ID_range)
    {
      mp_integer i=binary2integer(src, false);
      mp_integer from=string2integer(type.get_string(ID_from));
      value_expr.set(ID_value, integer2string(i+from));
    }
    else
      value_expr.set(ID_value, src);
  }
  else if(type.id()==ID_bool)
  {
    if(src=="0")
      value_expr=false_exprt();
    else if(src=="1")
      value_expr=true_exprt();
  }
  else if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);
    value_expr=exprt(ID_array, array_type);
    mp_integer size;
    to_integer(array_type.size(), size);
    unsigned size_int=integer2long(size);
    value_expr.operands().resize(size_int);
    unsigned op_width=src.size()/size_int;

    for(unsigned i=0; i<size_int; i++)
      value_expr.operands()[size_int-i-1]=bitstring_to_expr(
        std::string(src, i*op_width, op_width), array_type.subtype());
  }
  
  return value_expr;
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
         case tvt::tv_enumt::TV_TRUE: ch='1'; break;
         case tvt::tv_enumt::TV_FALSE: ch='0'; break;
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
          
