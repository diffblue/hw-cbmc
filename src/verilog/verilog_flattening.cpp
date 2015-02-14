/*******************************************************************\

Module: Verilog Flattening

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/std_expr.h>

#include "expr2verilog.h"
#include "verilog_flattening.h"
#include "verilog_expr.h"

/*******************************************************************\

Function: verilog_flatteningt::flatten_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_flatteningt::flatten_expr(exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    //irep_idt identifier=to_symbol_expr(expr).get_identifier();
    
  }
  else if(expr.id()==ID_function_call)
  {
    flatten_function_call(to_function_call_expr(expr));
  }
  else if(expr.has_operands())
    Forall_operands(it, expr)
      flatten_expr(*it);
}

/*******************************************************************\

Function: verilog_flatteningt::flatten_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_flatteningt::flatten_function_call(function_call_exprt &call)
{
  err_location(call);
  throw "support for function calls not implemented";
  //std::cout << call.pretty() << std::endl;
}

/*******************************************************************\

Function: verilog_flatteningt::replace_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_flatteningt::replace_symbols(
  const replace_mapt &what,
  exprt &dest)
{
  bool result=true;

  if(dest.id()==ID_next_symbol ||
     dest.id()==ID_symbol)
  {
    replace_mapt::const_iterator it=
      what.find(dest.get(ID_identifier));

    if(it!=what.end())
    {
      bool is_next_symbol=dest.id()==ID_next_symbol;
      dest=it->second;      

      if(is_next_symbol)
        replace_symbols(ID_next_symbol, dest);

      result=false;
    }
  }
  else
  {
    Forall_operands(it, dest)
      result=replace_symbols(what, *it) && result;
  }

  return result;
}

/*******************************************************************\

Function: verilog_flatteningt::replace_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_flatteningt::replace_symbols(
  const irep_idt &target,
  exprt &dest)
{
  if(dest.id()==ID_symbol)
    dest.id(target);
  else
    Forall_operands(it, dest)
      replace_symbols(target, *it);
}

/*******************************************************************\

Function: verilog_flatteningt::instantiate_port

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_flatteningt::instantiate_port(
  const exprt &symbol_expr,
  const exprt &value,
  const replace_mapt &replace_map)
{
  replace_mapt::const_iterator it=
    replace_map.find(symbol_expr.get(ID_identifier));

  if(it==replace_map.end())
  {
    str << "failed to find " << symbol_expr << " in replace_map";
    throw 0;
  }

  equal_exprt equality(it->second, value);

  if(equality.op0().type()!=equality.op1().type())
    equality.op0().make_typecast(equality.op1().type());

  verilog_continuous_assignt assign;

  assign.move_to_operands(equality);

  dest.push_back(assign);
}

/*******************************************************************\

Function: verilog_flatteningt::instantiate_ports

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_flatteningt::instantiate_ports(
  const irep_idt &instance,
  const exprt &inst,
  const symbolt &symbol,
  const replace_mapt &replace_map)
{
  const irept::subt &ports=symbol.type.find(ID_ports).get_sub();

  if(inst.operands().size()!=ports.size())
  {
    err_location(inst);
    str << "wrong number of ports: expected " << ports.size() 
        << " but got " << inst.operands().size() << std::endl; 
    str << inst.op0();
    throw 0;
  }

  if(inst.operands().size()==0)
    return;

  // named port connection?

  if(inst.op0().id()==ID_named_port_connection)
  {
    forall_operands(o_it, inst)
    {
      if(o_it->operands().size()==2)
      {
        const exprt &op0=o_it->op0();
        const exprt &op1=o_it->op1();

        if(op1.is_not_nil())
          instantiate_port(op0, op1, replace_map);
      }
    }
  }
  else // just a list without names
  {
    irept::subt::const_iterator p_it=
      ports.begin();

    forall_operands(o_it, inst)
    {
      instantiate_port(static_cast<const exprt &>(*p_it), *o_it,
                       replace_map);
      p_it++;
    }
  }
}

/*******************************************************************\

Function: verilog_flatteningt::flatten_inst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_flatteningt::flatten_inst(verilog_instt &inst)
{
  const irep_idt &identifier=inst.get(ID_module);

  // must be in symbol_table
  const symbolt &symbol=lookup(identifier);
    
  // make sure it's flat already
  verilog_flattening(
    symbol_table, identifier, get_message_handler(), options);

  assert(symbol.value.id()=="flat_verilog_module");

  forall_operands(it, inst)
    flatten_inst(symbol, *it);
    
  // kill it now
  exprt skip(ID_skip);
  skip.add_source_location()=inst.source_location();
  inst.swap(skip);
}

/*******************************************************************\

Function: verilog_flatteningt::flatten_inst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_flatteningt::flatten_inst(
  const symbolt &symbol,
  const exprt &op)
{
  const irep_idt &instance=op.get(ID_instance);

  std::list<irep_idt> new_symbols;
  replace_mapt replace_map;

  forall_symbol_module_map(it, symbol_table.symbol_module_map, symbol.module)
  {
    const symbolt &symbol=lookup(it->second);

    // don't replicate modules
    if(symbol.type.id()==ID_module)
      continue;

    // instantiate symbol

    symbolt new_symbol(symbol);

    new_symbol.module=module;
    new_symbol.hierarchy.push_front(id2string(module)+"."+id2string(instance));

    std::string full_identifier;

    full_identifier=mode+"::";
    full_identifier+=id2string(verilog_module_name(module));

    for(symbolt::hierarchyt::const_iterator
        it=new_symbol.hierarchy.begin();
        it!=new_symbol.hierarchy.end();
        it++)
      full_identifier+="."+id2string(lookup(*it).base_name);

    full_identifier+="."+id2string(symbol.base_name);

    new_symbol.name=full_identifier;

    if(symbol_table.add(new_symbol))
    {
      str << "name collision during module instantiation: "
          << new_symbol.name;
      throw 0;
    }

    new_symbols.push_back(new_symbol.name);

    // build replace map
    
    symbol_exprt new_symbol_expr;
    new_symbol_expr.type()=new_symbol.type;
    new_symbol_expr.set_identifier(new_symbol.name);

    std::pair<irep_idt, exprt> replace_pair;
    replace_pair.first=symbol.name;
    replace_pair.second=new_symbol_expr;
    replace_map.insert(replace_pair);
  }

  // replace identifiers in the replicated macros

  for(std::list<irep_idt>::const_iterator
      it=new_symbols.begin();
      it!=new_symbols.end();
      it++)
  {
    symbolt &symbol=symbol_table_lookup(*it);
    replace_symbols(replace_map, symbol.value);
  }

  // do the module body

  {
    exprt tmp=symbol.value;
    assert(tmp.id()=="flat_verilog_module");
    replace_symbols(replace_map, tmp);

    forall_operands(it, tmp)
      dest.push_back(*it);
  }

  instantiate_ports(instance, op, symbol, replace_map);
}

/*******************************************************************\

Function: verilog_flatteningt::flatten_module_item

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_flatteningt::flatten_module_item(
  verilog_module_itemt &module_item)
{
  if(module_item.id()==ID_inst)
    flatten_inst(to_verilog_inst(module_item));
  else
  {
    // generic fall-back
    flatten_expr(module_item);
  }
}

/*******************************************************************\

Function: verilog_flatteningt::flatten_module

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_flatteningt::flatten_module(symbolt &symbol)
{
  assert(symbol.value.id()==ID_verilog_module);

  // flatten the module items

  dest.clear();

  Forall_operands(it, symbol.value)
    flatten_module_item(static_cast<verilog_module_itemt &>(*it));

  // move "dest" to symbol.value

  symbol.value.operands().reserve(
    symbol.value.operands().size()+dest.size());
  
  for(unsigned i=0; i<dest.size(); i++)
    symbol.value.move_to_operands(dest[i]);
    
  // indicate we are done

  symbol.value.id("flat_verilog_module");
}

/*******************************************************************\

Function: verilog_flatteningt::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_flatteningt::typecheck()
{
  symbolt &symbol=symbol_table_lookup(module);
  // done already?
  if(symbol.value.id()=="flat_verilog_module") return;
  flatten_module(symbol);
}

/*******************************************************************\

Function: verilog_flattening

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_flattening(
  symbol_tablet &symbol_table,
  const irep_idt &module,
  message_handlert &message_handler,
  const optionst &options)
{
  verilog_flatteningt verilog_flattening(
    symbol_table, module, options, message_handler);
  return verilog_flattening.typecheck_main();
}
