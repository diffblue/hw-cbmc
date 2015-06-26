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

#include "instantiate.h"
#include "trans_trace.h"

/*******************************************************************\

Function: trans_tracet::get_max_failing_timeframe

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned trans_tracet::get_max_failing_timeframe() const
{
  assert(!states.empty());
  if(properties.empty()) return states.size()-1;
  
  unsigned max=0;
  
  for(propertiest::const_iterator
      it=properties.begin();
      it!=properties.end();
      it++)
  {
    if(it->status.is_false() &&
       it->failing_timeframe>max)
      max=it->failing_timeframe;
  }
  
  return max;
}

/*******************************************************************\

Function: trans_tracet::get_min_failing_timeframe

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned trans_tracet::get_min_failing_timeframe() const
{
  assert(!states.empty());
  if(properties.empty()) return states.size()-1;
  
  unsigned min=states.size()-1;
  
  for(propertiest::const_iterator
      it=properties.begin();
      it!=properties.end();
      it++)
  {
    if(it->status.is_false() && it->failing_timeframe<min)
      min=it->failing_timeframe;
  }
  
  return min;
}

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
  const std::list<bvt> &prop_bv,
  const propt &solver,
  unsigned no_timeframes,
  trans_tracet &dest)  
{
  // check the properties that got violated

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
      dest.properties.back().status=tvt(tvt::TV_UNKNOWN);
    else
      dest.properties.back().status=tvt(true);
  }
}

/*******************************************************************\

Function: compute_trans_trace_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void compute_trans_trace_properties(
  const std::list<bvt> &prop_bv,
  const prop_convt &solver,
  unsigned no_timeframes,
  trans_tracet &dest)  
{
  // check the properties that got violated

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
      dest.properties.back().status=tvt(tvt::TV_UNKNOWN);
    else
      dest.properties.back().status=tvt(true);
  }
}

/*******************************************************************\

Function: compute_trans_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void compute_trans_trace(
  const std::list<bvt> &prop_bv,
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
  
  compute_trans_trace_properties(
    prop_bv,
    solver,
    no_timeframes,
    dest);
}

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
  const std::list<bvt> &prop_bv,
  const bmc_mapt &bmc_map,
  const propt &solver,
  const namespacet &ns,
  trans_tracet &dest)
{
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
    prop_bv,
    solver,
    bmc_map.get_no_timeframes(),
    dest);
}         
          
/*******************************************************************\

Function: show_trans_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_trans_state(
  unsigned timeframe,
  const trans_tracet::statet &state,
  const namespacet &ns)
{
  std::cout << "Transition system state " << timeframe << "\n";
  std::cout << "----------------------------------------------------\n";

  for(trans_tracet::statet::assignmentst::const_iterator
      it=state.assignments.begin();
      it!=state.assignments.end();
      it++)
  {
    assert(it->lhs.id()==ID_symbol);

    const symbolt &symbol=ns.lookup(it->lhs.get(ID_identifier));
    
    if(symbol.is_auxiliary)
      continue;

    std::cout << "  " << symbol.display_name() << " = ";

    const exprt &rhs=it->rhs;

    if(rhs.is_nil())
      std::cout << "?";
    else
      std::cout << from_expr(ns, symbol.name, rhs);
    
    if(rhs.type().id()==ID_unsignedbv ||
       rhs.type().id()==ID_signedbv ||
       rhs.type().id()==ID_bv)
    {
      unsigned width=rhs.type().get_int(ID_width);
      
      if(width>=2 && width<=32 &&
         rhs.id()==ID_constant)
        std::cout << " (" << rhs.get(ID_value) << ")";
    }
    
    std::cout << '\n';
  }

  std::cout << std::endl;
}

/*******************************************************************\

Function: convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert(
  const trans_tracet &trace,
  unsigned last_time_frame,
  const namespacet &ns,
  xmlt &dest)
{
  dest=xmlt("trans_trace");
  
  dest.new_element("mode").data=trace.mode;

  for(unsigned t=0; t<=last_time_frame; t++)
  {
    assert(t<trace.states.size());
  
    xmlt &xml_state=dest.new_element("state");
    const trans_tracet::statet &state=trace.states[t];

    xml_state.new_element("timeframe").data=i2string(t); // will go away
    xml_state.set_attribute("timeframe", t);
    
    for(trans_tracet::statet::assignmentst::const_iterator
        it=state.assignments.begin();
        it!=state.assignments.end();
        it++)
    {
      xmlt &xml_assignment=xml_state.new_element("assignment");

      assert(it->lhs.id()==ID_symbol);
      const symbolt &symbol=ns.lookup(it->lhs.get(ID_identifier));

      std::string value_string=from_expr(ns, symbol.name, it->rhs);
      std::string type_string=from_type(ns, symbol.name, symbol.type);

      if(it->rhs.is_nil())
        value_string="?";
      else
        xml_assignment.new_element("value_expression").new_element(xml(it->rhs, ns));

      xml_assignment.new_element("identifier").data=id2string(symbol.name);
      xml_assignment.new_element("base_name").data=id2string(symbol.base_name);
      xml_assignment.new_element("display_name").data=id2string(symbol.display_name());
      xml_assignment.new_element("value").data=value_string;
      xml_assignment.new_element("type").data=type_string;
      xml_assignment.new_element("mode").data=id2string(symbol.mode);

      #if 0
      if(it->location.is_not_nil())
      {
        xmlt &xml_location=xml_assignment.new_element();

        convert(it->location, xml_location);
        xml_location.name="location";
      }
      #endif
    }
  }

  {
    unsigned p=1;

    for(trans_tracet::propertiest::const_iterator
        p_it=trace.properties.begin();
        p_it!=trace.properties.end();
        p_it++, p++)
    {
      xmlt &xml_claim_status=dest.new_element("claim-status");
      
      xml_claim_status.new_element("claim").data=i2string(p);
      
      if(p_it->status.is_false())
      {
        xml_claim_status.new_element("time_frame").data=
          i2string(p_it->failing_timeframe);

        xml_claim_status.new_element("status").data="false";
      }
      else if(p_it->status.is_true())
        xml_claim_status.new_element("status").data="true";
      else
        xml_claim_status.new_element("status").data="unknown";
    }
  }
}

/*******************************************************************\

Function: show_trans_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_trans_trace(
  const trans_tracet &trace,
  messaget &message,
  const namespacet &ns,
  ui_message_handlert::uit ui)
{
  unsigned l=trace.get_max_failing_timeframe();

  switch(ui)
  {
  case ui_message_handlert::PLAIN:
    for(unsigned t=0; t<=l; t++)
      show_trans_state(t, trace.states[t], ns);

    {
      unsigned p=1;

      for(trans_tracet::propertiest::const_iterator
          p_it=trace.properties.begin();
          p_it!=trace.properties.end();
          p_it++, p++)
        if(p_it->status.is_false())
        {
          std::cout << "Property " << p << " violated in "
                       "time frame " << p_it->failing_timeframe
                    << '\n';
        }
    }
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml;
      
      convert(trace, l, ns, xml);
      
      xml.output(std::cout);
    }
    break;
    
  default:
    assert(false);
  }
}

/*******************************************************************\

Function: vcd_width

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static mp_integer vcd_width(
  const typet &type,
  const namespacet &ns)
{
  if(type.id()==ID_symbol)
    return vcd_width(ns.follow(type), ns);
  else if(type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv ||
          type.id()==ID_bv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_floatbv ||
          type.id()==ID_pointer)
    return string2integer(type.get_string(ID_width));
  else if(type.id()==ID_array)
  {
    mp_integer sub=vcd_width(type.subtype(), ns);
  
    // get size
    const exprt &size=to_array_type(type).size();

    // constant?
    mp_integer i;
    
    if(to_integer(size, i))
      return -1; // we cannot distinguish the elements
    
    return sub*i;
  }
  else if(type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(type);
    const struct_typet::componentst &components=
      struct_type.components();
      
    mp_integer result=0;
    
    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      const typet &subtype=it->type();
      mp_integer sub_size=pointer_offset_size(subtype, ns);
      if(sub_size==-1) return -1;
      result+=sub_size;
    }
    
    return result;
  }
  else if(type.id()==ID_bool)
    return 1;
  else if(type.id()==ID_integer)
    return 32; // no better idea.
  else
    return -1;
}

/*******************************************************************\

Function: as_vcd_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static std::string as_vcd_binary(
  const exprt &expr,
  const namespacet &ns)
{
  const typet &type=ns.follow(expr.type());
  
  if(expr.id()==ID_constant)
  {
    if(type.id()==ID_unsignedbv ||
       type.id()==ID_signedbv ||
       type.id()==ID_bv ||
       type.id()==ID_fixedbv ||
       type.id()==ID_floatbv ||
       type.id()==ID_pointer)
      return expr.get_string(ID_value);
    else if(type.id()==ID_integer)
    {
      mp_integer i;
      if(!to_integer(expr, i))
        return integer2binary(i, 32); // 32 is hardwired
    }
  }
  else if(expr.id()==ID_array)
  {
    std::string result;

    forall_operands(it, expr)
      result+=as_vcd_binary(*it, ns);
    
    return result;
  }
  else if(expr.id()==ID_struct)
  {
    std::string result;

    forall_operands(it, expr)
      result+=as_vcd_binary(*it, ns);
    
    return result;
  }
  else if(expr.id()==ID_union)
  { 
    assert(expr.operands().size()==1);
    return as_vcd_binary(expr.op0(), ns);
  }

  // build "xxx"

  mp_integer width=vcd_width(type, ns);

  if(width>=0)
  {
    std::string result;

    for(; width!=0; --width)
      result+='x';

    return result;
  }
  
  return "";
}

/*******************************************************************\

Function: vcd_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string vcd_identifier(const std::string &id)
{
  std::string result=id;

  if((has_prefix(result, "verilog::")) || (has_prefix(result, "Verilog::")))
    result.erase(0, 9);
  else if(has_prefix(result, "smv::"))
    result.erase(0, 5);
    
  return result;
}

/*******************************************************************\

Function: show_trans_state_vcd

  Inputs:

 Outputs:

 Purpose: dumps the counterexample state in vcd format to be
          viewed in modelsim or any other simulator

\*******************************************************************/

void show_trans_state_vcd(
  unsigned timeframe,
  const trans_tracet::statet &previous_state,
  const trans_tracet::statet &current_state,
  const namespacet &ns,
  std::ostream &out)
{
  out << "#" << timeframe << '\n';

  // build map for previous state  
  std::map<irep_idt, exprt> previous_values;

  for(trans_tracet::statet::assignmentst::const_iterator
      it=previous_state.assignments.begin();
      it!=previous_state.assignments.end();
      it++)
    previous_values[it->lhs.get(ID_identifier)]=it->rhs;

  // now dump current state
  for(trans_tracet::statet::assignmentst::const_iterator
      it=current_state.assignments.begin();
      it!=current_state.assignments.end();
      it++)
  {
    assert(it->lhs.id()==ID_symbol);

    const symbolt &symbol=ns.lookup(it->lhs.get(ID_identifier));
    
    if(symbol.is_auxiliary)
      continue;
    
    if(timeframe!=0)
      if(previous_values[symbol.name]==it->rhs)
        continue; // value didn't change!
  
    if(it->rhs.is_nil()) // no value
      continue;
  
    std::string display_name=id2string(symbol.display_name());

    if(it->lhs.type().id()==ID_bool)
    {
      // booleans are special -- no space!

      if(it->rhs.is_true())
        out << '1' << vcd_identifier(display_name) << '\n';
      else if(it->rhs.is_false())
        out << '0' << vcd_identifier(display_name) << '\n';
      else
        out << 'x' << vcd_identifier(display_name) << '\n';
    }
    else
    {
      out << 'b' << as_vcd_binary(it->rhs, ns) << ' '
          << vcd_identifier(display_name) << '\n';
    }
  }
}

/*******************************************************************\

Function: vcd_suffix

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static std::string vcd_suffix(
  const typet &type,
  const namespacet &ns)
{
  if(type.id()==ID_unsignedbv ||
     type.id()==ID_signedbv ||
     type.id()==ID_bv ||
     type.id()==ID_fixedbv ||
     type.id()==ID_floatbv ||
     type.id()==ID_verilogbv)
  {
    mp_integer width=vcd_width(type, ns);
    mp_integer offset=string2integer(type.get_string(ID_C_offset));

    mp_integer left_bound, right_bound;

    left_bound = offset;
    right_bound = left_bound+width-1;

    if(type.get_bool(ID_C_little_endian))
      std::swap(left_bound, right_bound);
    
    return "["+integer2string(left_bound)+":"+integer2string(right_bound)+"]";
  }
  else if(type.id()==ID_array)
  {
    // get size
    const exprt &size=to_array_type(type).size();

    // constant?
    mp_integer i;
    
    if(to_integer(size, i))
      return ""; // we cannot distinguish the elements

    mp_integer left_bound, right_bound;
    left_bound=0;
    right_bound=left_bound+i-1;

    return"["+integer2string(left_bound)+":"+integer2string(right_bound)+"]"+
          vcd_suffix(type.subtype(), ns);
  }
  else if(type.id()==ID_bool)
    return "";
  else if(type.id()==ID_integer)
    return "";
  else
  {
    mp_integer width=vcd_width(type, ns);
    mp_integer left_bound, right_bound;
    left_bound=0;
    right_bound=left_bound+width-1;
    return "["+integer2string(left_bound)+":"+integer2string(right_bound)+"]";
  }
}

/*******************************************************************\

Function: vcd_hierarchy_rec

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void vcd_hierarchy_rec(
  const namespacet &ns,
  const std::set<irep_idt> &ids,
  const std::string &prefix,
  std::ostream &out,
  unsigned depth)
{
  std::set<std::string> sub_modules;
  std::set<irep_idt> signals;
  
  for(std::set<irep_idt>::const_iterator
      it=ids.begin();
      it!=ids.end();
      it++)
  {
    if(has_prefix(id2string(*it), prefix))
    {
      std::string rest=
        std::string(id2string(*it), prefix.size(), std::string::npos);
      std::size_t dot_pos=rest.find('.');
      if(dot_pos==std::string::npos)
        signals.insert(*it);
      else
        sub_modules.insert(std::string(rest, 0, dot_pos));
    }
  }

  // do signals first
  for(std::set<irep_idt>::const_iterator
      it=signals.begin();
      it!=signals.end();
      it++)
  {
    const symbolt &symbol=ns.lookup(*it);
    
    if(symbol.is_auxiliary) continue;

    std::string display_name = id2string(symbol.display_name());
    
    std::string signal_class;
    
    if(symbol.type.id()==ID_integer)
      signal_class="integer";
    else if(symbol.is_state_var)
      signal_class="reg";
    else
      signal_class="wire";

    mp_integer width=vcd_width(symbol.type, ns);
    
    std::string suffix=vcd_suffix(symbol.type, ns);
    
    if(width>=1)
      out << std::string(depth*2, ' ')
          << "$var " << signal_class << " "
          << width << " "
          << vcd_identifier(display_name) << " " 
          << vcd_identifier(display_name)
          << (suffix==""?"":" ") << suffix
          << " $end" << '\n';
  }
  
  // now do sub modules
  for(std::set<std::string>::const_iterator
      it=sub_modules.begin();
      it!=sub_modules.end();
      it++)
  {
    out << std::string(depth*2, ' ')
        << "$scope module " << *it << " $end\n";

    // recursive call
    vcd_hierarchy_rec(ns, ids, prefix+*it+".", out, depth+1);
    
    out << std::string(depth*2, ' ')
        << "$upscope $end\n";
  }
};

/*******************************************************************\

Function: show_trans_trace_vcd

  Inputs:

 Outputs:

 Purpose: dumps the counterexample trace in vcd format to be
          viewed in modelsim or any other simulator

\*******************************************************************/

void show_trans_trace_vcd(
  const trans_tracet &trace,
  messaget &message,
  const namespacet &ns,
  std::ostream &out)
{
  time_t t;
  time(&t);
  out << "$date\n  " << ctime(&t) << "$end" << '\n';

  out << "$timescale\n  1ns\n$end" << '\n';
  
  if(trace.states.empty()) return;

  const trans_tracet::statet &state=trace.states[0];

  assert(!state.assignments.empty());

  const symbolt &symbol1=ns.lookup(
    state.assignments.front().lhs.get(ID_identifier));

  std::string module_name=id2string(symbol1.module);
  out << "$scope module " << vcd_identifier(module_name) << " $end\n";
  
  // get identifiers
  std::set<irep_idt> ids;
  
  for(trans_tracet::statet::assignmentst::const_iterator
      it=state.assignments.begin();
      it!=state.assignments.end();
      it++)
  {
    assert(it->lhs.id()==ID_symbol);
    ids.insert(it->lhs.get(ID_identifier));
  }
  
  // split up into hierarchy
  vcd_hierarchy_rec(ns, ids, module_name+".", out, 1);
  
  out << "$upscope $end\n";  

  out << "$enddefinitions $end\n";
  
  unsigned l=trace.get_max_failing_timeframe();
  
  // initial state

  show_trans_state_vcd(0, trace.states[0], trace.states[0], ns, out);
  
  // following ones

  for(unsigned t=1; t<=l; t++)
    show_trans_state_vcd(t, trace.states[t-1], trace.states[t], ns, out);
}

