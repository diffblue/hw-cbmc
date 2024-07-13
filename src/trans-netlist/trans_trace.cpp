/*******************************************************************\

Module: Extracting Counterexamples

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "trans_trace.h"

#include <util/ebmc_util.h>
#include <util/expr_util.h>
#include <util/json_irep.h>
#include <util/pointer_offset_size.h>
#include <util/prefix.h>
#include <util/std_expr.h>
#include <util/xml.h>

#include <goto-programs/xml_expr.h>

#include <langapi/language_util.h>

#include "instantiate_netlist.h"

#include <cassert>
#include <ctime>
#include <iostream>
#include <string>

#include "../trans-word-level/instantiate_word_level.h"

/*******************************************************************\

Function: trans_tracet::get_max_failing_timeframe

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::optional<std::size_t> trans_tracet::get_max_failing_timeframe() const
{
  std::optional<std::size_t> max = {};

  for(std::size_t t = 0; t < states.size(); t++)
  {
    if(states[t].property_failed)
      max=t;
  }
  
  return max;
}

/*******************************************************************\

Function: trans_tracet::get_min_failing_timeframe

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::optional<std::size_t> trans_tracet::get_min_failing_timeframe() const
{
  for(std::size_t t = 0; t < states.size(); t++)
    if(states[t].property_failed)
      return t;

  return {};
}

/*******************************************************************\

Function: bvrep2binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string bvrep2binary(const constant_exprt &expr)
{
  const auto &value = expr.get_value();
  std::size_t width = to_bitvector_type(expr.type()).get_width();
  std::string result;
  result.reserve(width);
  for(std::size_t dest_index = 0; dest_index < width; dest_index++)
    result.push_back(
      get_bvrep_bit(value, width, width - dest_index - 1) ? '1' : '0');
  return result;
}

/*******************************************************************\

Function: show_trans_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_trans_state(
  std::size_t timeframe,
  const trans_tracet::statet &state,
  const namespacet &ns)
{
  std::cout << "Transition system state " << timeframe << "\n";
  std::cout << "----------------------------------------------------\n";

  for(const auto & a : state.assignments)
  {
    assert(a.lhs.id()==ID_symbol);

    const symbolt &symbol=ns.lookup(to_symbol_expr(a.lhs));
    
    if(symbol.is_auxiliary)
      continue;

    std::cout << "  " << symbol.display_name() << " = ";

    const exprt &rhs=a.rhs;

    if(rhs.is_nil())
      std::cout << "?";
    else
      std::cout << from_expr(ns, symbol.name, rhs);

    if(rhs.type().id() == ID_unsignedbv || rhs.type().id() == ID_signedbv)
    {
      std::size_t width=to_bitvector_type(rhs.type()).get_width();

      if(width >= 2 && width <= 32 && rhs.id() == ID_constant)
      {
        std::cout << " ("
                  << integer2binary(
                       numeric_cast_v<mp_integer>(to_constant_expr(rhs)), width)
                  << ')';
      }
    }
    else if(rhs.type().id() == ID_bv)
    {
      std::size_t width = to_bv_type(rhs.type()).get_width();

      if(width>=2 && width<=32 &&
         rhs.id()==ID_constant)
      {
        std::cout << " (" << bvrep2binary(to_constant_expr(rhs)) << ')';
      }
    }

    std::cout << '\n';
  }

  std::cout << '\n' << std::flush;
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
  std::ostream &out)
{
  PRECONDITION(!trace.states.empty());

  auto l = trace.get_min_failing_timeframe().value_or(trace.states.size() - 1);

  for(std::size_t t = 0; t <= l; t++)
    show_trans_state(t, trace.states[t], ns);
}

/*******************************************************************\

Function: xml

  Inputs:

 Outputs:

 Purpose: Transform trans_tracet to XML

\*******************************************************************/

xmlt xml(const trans_tracet &trace, const namespacet &ns)
{
  PRECONDITION(!trace.states.empty());

  auto min_failing_timeframe_opt = trace.get_min_failing_timeframe();

  auto last_time_frame =
    min_failing_timeframe_opt.value_or(trace.states.size() - 1);

  xmlt dest = xmlt{"trans_trace"};

  dest.new_element("mode").data=trace.mode;

  for(std::size_t t = 0; t <= last_time_frame; t++)
  {
    assert(t<trace.states.size());
  
    xmlt &xml_state=dest.new_element("state");
    const trans_tracet::statet &state=trace.states[t];

    xml_state.new_element("timeframe").data=std::to_string(t); // will go away
    xml_state.set_attribute("timeframe", t);
    
    for(const auto & a : state.assignments)
    {
      xmlt &xml_assignment=xml_state.new_element("assignment");

      assert(a.lhs.id()==ID_symbol);
      const symbolt &symbol=ns.lookup(to_symbol_expr(a.lhs));

      std::string value_string=from_expr(ns, symbol.name, a.rhs);
      std::string type_string=from_type(ns, symbol.name, symbol.type);

      if(a.rhs.is_nil())
        value_string="?";
      else
        xml_assignment.new_element("value_expression").new_element(xml(a.rhs, ns));

      xml_assignment.new_element("identifier").data=id2string(symbol.name);
      xml_assignment.new_element("base_name").data=id2string(symbol.base_name);
      xml_assignment.new_element("display_name").data=id2string(symbol.display_name());
      xml_assignment.new_element("value").data=value_string;
      xml_assignment.new_element("type").data=type_string;
      xml_assignment.new_element("mode").data=id2string(symbol.mode);

      #if 0
      if(a.location.is_not_nil())
      {
        xmlt &xml_location=xml_assignment.new_element();

        convert(a.location, xml_location);
        xml_location.name="location";
      }
      #endif
    }
  }

  return dest;
}

/*******************************************************************\

Function: json

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

jsont json(const trans_tracet &trace, const namespacet &ns)
{
  json_objectt json_trace;

  json_trace["mode"] = json_stringt(trace.mode);
  json_arrayt &json_states = json_trace["states"].make_array();

  for(auto &state : trace.states)
  {
    json_arrayt json_assignments;

    for(const auto &a : state.assignments)
    {
      json_objectt json_assignment;

      DATA_INVARIANT(a.lhs.id() == ID_symbol, "assignment lhs must be symbol");
      const symbolt &symbol = ns.lookup(to_symbol_expr(a.lhs));

      if(symbol.is_auxiliary)
        continue; // drop

      std::string lhs_string = from_expr(ns, symbol.name, a.lhs);

      std::string value_string =
        a.rhs.is_nil() ? "" : from_expr(ns, symbol.name, a.rhs);

      std::string type_string = from_type(ns, symbol.name, symbol.type);

      json_assignment["lhs"] = json_stringt(lhs_string);
      json_assignment["identifier"] = json_stringt(id2string(symbol.name));
      json_assignment["base_name"] = json_stringt(id2string(symbol.base_name));
      json_assignment["display_name"] =
        json_stringt(id2string(symbol.display_name()));
      json_assignment["value"] = json_stringt(value_string);
      json_assignment["lhs_type"] = json_stringt(type_string);
      json_assignment["mode"] = json_stringt(id2string(symbol.mode));
      json_assignment["state_var"] = jsont::json_boolean(symbol.is_state_var);

      if(a.location.is_not_nil())
        json_assignment["location"] = json(a.location);

      json_assignments.push_back(std::move(json_assignment));
    }

    json_states.push_back(std::move(json_assignments));

    if(state.property_failed)
      break; // done
  }

  return std::move(json_trace);
}

/*******************************************************************\

Function: show_trans_trace_xml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_trans_trace_xml(
  const trans_tracet &trace,
  messaget &,
  const namespacet &ns,
  std::ostream &out)
{
  xml(trace, ns).output(out);
}

/*******************************************************************\

Function: show_trans_trace_json

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_trans_trace_json(
  const trans_tracet &trace,
  messaget &,
  const namespacet &ns,
  std::ostream &out)
{
  out << json(trace, ns);
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
  {
    return to_bitvector_type(type).get_width();
  }
  else if(type.id()==ID_array)
  {
    auto &array_type = to_array_type(type);
    mp_integer sub = vcd_width(array_type.element_type(), ns);

    // get size
    const exprt &size = array_type.size();

    // constant?
    mp_integer i;

    if(to_integer_non_constant(size, i))
      return -1; // we cannot distinguish the elements
    
    return sub*i;
  }
  else if(type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(type);
    const struct_typet::componentst &components=
      struct_type.components();
      
    mp_integer result=0;
    
    for(const auto & it : components)
    {
      const typet &subtype=it.type();
      mp_integer sub_size = *pointer_offset_size(subtype, ns);
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
    if(
      type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
      type.id() == ID_bv || type.id() == ID_fixedbv ||
      type.id() == ID_floatbv || type.id() == ID_pointer ||
      type.id() == ID_integer)
    {
      mp_integer i = numeric_cast_v<mp_integer>(to_constant_expr(expr));
      auto width = numeric_cast_v<std::size_t>(vcd_width(type, ns));
      return integer2binary(i, width);
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
    return as_vcd_binary(to_union_expr(expr).op(), ns);
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

Function: vcd_reference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string vcd_reference(const symbolt &symbol, const std::string &prefix)
{
  std::string result = id2string(symbol.name);

  if(!prefix.empty() && has_prefix(result, prefix))
    result.erase(0, prefix.size());

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
  std::size_t timeframe,
  const trans_tracet::statet &previous_state,
  const trans_tracet::statet &current_state,
  const namespacet &ns,
  std::ostream &out)
{
  out << "#" << timeframe << '\n';

  // build map for previous state  
  std::map<irep_idt, exprt> previous_values;

  for(const auto & a : previous_state.assignments)
    previous_values[a.lhs.get(ID_identifier)]=a.rhs;

  // now dump current state
  for(const auto & a : current_state.assignments)
  {
    assert(a.lhs.id()==ID_symbol);

    const symbolt &symbol=
      ns.lookup(to_symbol_expr(a.lhs));
    
    if(symbol.is_auxiliary)
      continue;
    
    if(timeframe!=0)
      if(previous_values[symbol.name]==a.rhs)
        continue; // value didn't change!
  
    if(a.rhs.is_nil()) // no value
      continue;
  
    std::string display_name=id2string(symbol.display_name());

    if(a.lhs.type().id()==ID_bool)
    {
      // booleans are special -- no space!

      if(a.rhs.is_true())
        out << '1' << vcd_identifier(display_name) << '\n';
      else if(a.rhs.is_false())
        out << '0' << vcd_identifier(display_name) << '\n';
      else
        out << 'x' << vcd_identifier(display_name) << '\n';
    }
    else
    {
      out << 'b' << as_vcd_binary(a.rhs, ns) << ' '
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
     type.id()==ID_verilog_signedbv ||
     type.id()==ID_verilog_unsignedbv)
  {
    mp_integer width=vcd_width(type, ns);
    mp_integer offset=string2integer(type.get_string(ID_C_offset));

    mp_integer left_bound, right_bound;

    left_bound = offset;
    right_bound = left_bound+width-1;

    if(!type.get_bool(ID_C_big_endian))
      std::swap(left_bound, right_bound);
    
    return "["+integer2string(left_bound)+":"+integer2string(right_bound)+"]";
  }
  else if(type.id()==ID_array)
  {
    // get size
    auto &array_type = to_array_type(type);
    const exprt &size = array_type.size();

    // constant?
    mp_integer i;

    if(to_integer_non_constant(size, i))
      return ""; // we cannot distinguish the elements

    mp_integer left_bound, right_bound;
    left_bound=0;
    right_bound=left_bound+i-1;

    return "[" + integer2string(left_bound) + ":" +
           integer2string(right_bound) + "]" +
           vcd_suffix(array_type.element_type(), ns);
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
  std::size_t depth)
{
  std::set<std::string> sub_modules;
  std::set<irep_idt> signals;
  
  for(const auto & it : ids)
  {
    if(has_prefix(id2string(it), prefix))
    {
      std::string rest=
        std::string(id2string(it), prefix.size(), std::string::npos);
      std::size_t dot_pos=rest.find('.');
      if(dot_pos==std::string::npos)
        signals.insert(it);
      else
        sub_modules.insert(std::string(rest, 0, dot_pos));
    }
  }

  // do signals first
  for(const auto & it : signals)
  {
    const symbolt &symbol=ns.lookup(it);
    
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
      out << std::string(depth * 2, ' ') << "$var " << signal_class << " "
          << width << " " << vcd_identifier(display_name) << " "
          << vcd_reference(symbol, prefix) << (suffix == "" ? "" : " ")
          << suffix << " $end" << '\n';
  }
  
  // now do sub modules
  for(const auto & identifier : sub_modules)
  {
    out << std::string(depth*2, ' ')
        << "$scope module " << identifier << " $end\n";

    // recursive call
    vcd_hierarchy_rec(ns, ids, prefix+identifier+".", out, depth+1);
    
    out << std::string(depth*2, ' ')
        << "$upscope $end\n";
  }
}

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

  // get identifiers
  std::set<irep_idt> ids;
  
  for(const auto & a : state.assignments)
  {
    assert(a.lhs.id()==ID_symbol);
    ids.insert(to_symbol_expr(a.lhs).get_identifier());
  }

  // determine module

  const symbolt &symbol1 =
    ns.lookup(state.assignments.front().lhs.get(ID_identifier));

  auto &module_symbol = ns.lookup(symbol1.module);

  // print those in the top module

  out << "$scope module " << module_symbol.display_name() << " $end\n";

  // split up into hierarchy
  vcd_hierarchy_rec(ns, ids, id2string(module_symbol.name) + ".", out, 1);

  out << "$upscope $end\n";  

  out << "$enddefinitions $end\n";

  auto l = trace.get_min_failing_timeframe().value_or(trace.states.size() - 1);

  // initial state

  show_trans_state_vcd(0, trace.states[0], trace.states[0], ns, out);
  
  // following ones

  for(std::size_t t = 1; t <= l; t++)
    show_trans_state_vcd(t, trace.states[t-1], trace.states[t], ns, out);
}

/*******************************************************************\

Function: show_trans_state_numbered

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_trans_state_numbered(
  std::size_t timeframe,
  const trans_tracet::statet &state,
  const namespacet &ns)
{
  for(const auto &a : state.assignments)
  {
    DATA_INVARIANT(
      a.lhs.id() == ID_symbol, "trace assignment lhs must be symbol");

    const symbolt &symbol = ns.lookup(to_symbol_expr(a.lhs));

    std::cout << symbol.display_name() << '@' << timeframe << " = ";

    const exprt &rhs = a.rhs;

    if(rhs.is_nil())
      std::cout << "?";
    else
      std::cout << from_expr(ns, symbol.name, rhs);

    std::cout << '\n';
  }
}

/*******************************************************************\

Function: show_trans_trace_numbered

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_trans_trace_numbered(
  const trans_tracet &trace,
  messaget &message,
  const namespacet &ns,
  std::ostream &out)
{
  PRECONDITION(!trace.states.empty());

  auto l = trace.get_min_failing_timeframe().value_or(trace.states.size() - 1);

  for(std::size_t t = 0; t <= l; t++)
    show_trans_state_numbered(t, trace.states[t], ns);
}
