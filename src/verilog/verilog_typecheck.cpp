/*******************************************************************\

Module: Verilog Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <map>
#include <set>

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/simplify_expr.h>
#include <util/replace_symbol.h>
#include <util/i2string.h>
#include <util/std_expr.h>

#include "expr2verilog.h"
#include "verilog_typecheck.h"
#include "verilog_expr.h"
#include "verilog_types.h"

/*******************************************************************\

Function: verilog_typecheckt::array_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

array_typet verilog_typecheckt::array_type(
  const irept &src,
  const typet &element_type)
{
  assert(src.id()==ID_array);
  
  mp_integer msb, lsb;
  const exprt &range=static_cast<const exprt &>(src.find(ID_range));

  convert_range(range, msb, lsb);

  bool little_endian=(lsb<=msb);

  mp_integer size=(little_endian?msb-lsb:lsb-msb)+1;
  mp_integer offset=little_endian?lsb:msb;

  if(size<=0)
  {
    error().source_location=range.find_source_location();
    error() << "array size must be positive" << eom;
  }
  
  const typet src_subtype=
    static_cast<const typet &>(src).subtype();
  
  typet array_subtype;
  
  // may need to go recursive
  if(src_subtype.is_nil())
    array_subtype=element_type;
  else
    array_subtype=array_type(src_subtype, element_type);

  const exprt size_expr=from_integer(size, natural_typet());
  array_typet result(array_subtype, size_expr);
  result.set(ID_offset, from_integer(offset, natural_typet()));
  result.set(ID_C_little_endian, little_endian);
  
  return result;
}

/*******************************************************************\

Function: verilog_typecheckt::typecheck_port_connection

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::typecheck_port_connection(
  exprt &op,
  const exprt &port)
{
  const symbolt &symbol=
    lookup(port.get(ID_identifier));

  if(!symbol.is_input && !symbol.is_output)
  {
    error().source_location=op.source_location();
    error() << "port `" << symbol.name
        << "' is neither input nor output";
    throw 0;
  }

  if(op.is_nil())
  {
    // *not* connected
  }
  else
  {
    convert_expr(op);
   
    if(symbol.is_output)
      check_lhs(op, A_CONTINUOUS);
    else
      propagate_type(op, port.type());
  }
}

/*******************************************************************\

Function: verilog_typecheckt::typecheck_port_connections

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::typecheck_port_connections(
  exprt &inst,
  const symbolt &symbol)
{
  const exprt &range=static_cast<const exprt &>(inst.find(ID_range));

  mp_integer msb, lsb;
  
  if(range.is_nil() || range.id()==irep_idt())
    msb=lsb=0;
  else
    convert_range(range, msb, lsb);

  const irept::subt &ports=symbol.type.find(ID_ports).get_sub();

  // no arguments is one argument that is nil  
  if(ports.size()==0 && inst.operands().size()==1 &&
     inst.operands().front().is_nil())
    inst.operands().clear();

  if(inst.operands().empty())
  {
    if(!ports.empty())
    {
      error().source_location=inst.source_location();
      error() << "module does not have ports";
      throw 0;
    }

    return;
  }

  // named port connection?

  if(inst.op0().id()==ID_named_port_connection)
  {
    // We don't require that all ports are connected.
  
    std::set<irep_idt> assigned_ports;

    Forall_operands(o_it, inst)
    {
      if(o_it->id()!=ID_named_port_connection ||
         o_it->operands().size()!=2)
      {
        error().source_location=inst.source_location();
        error() << "expected a named port connection" << eom;
        throw 0;
      }

      exprt &op=o_it->op1();
      const irep_idt &name=
        o_it->op0().get(ID_identifier);

      bool found=false;

      std::string identifier=
        id2string(symbol.module)+"."+id2string(name);

      o_it->op0().set(ID_identifier, identifier);

      if(assigned_ports.find(name)!=
         assigned_ports.end())
      {
        error().source_location=o_it->source_location();
        error() << "port name " << name << " assigned twice";
        throw 0;
      }

      forall_irep(p_it, ports)
      {
        if(p_it->get(ID_identifier)==identifier)
        {
          const exprt &p_expr=(exprt &)(*p_it);
          found=true;
          typecheck_port_connection(op, p_expr);
          o_it->op0().type()=p_expr.type();
          break;
        }
      }

      if(!found)
      {
        error().source_location=o_it->source_location();
        error() << "port name " << identifier << " not found";
        throw 0;
      }

      assigned_ports.insert(identifier);
    }
  }
  else // just a list without names
  {
    if(inst.operands().size()!=ports.size())
    {
      error().source_location=inst.source_location();
      error() << "wrong number of arguments: expected " << ports.size() 
          << " but got " << inst.operands().size(); 
      throw 0;
    }

    irept::subt::const_iterator p_it=
      ports.begin();

    Forall_operands(o_it, inst)
    {
      typecheck_port_connection(*o_it, (exprt &)*p_it);
      p_it++;
    }
  }
}

/*******************************************************************\

Function: verilog_typecheckt::typecheck_builtin_port_connections

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::typecheck_builtin_port_connections(
  exprt &inst)
{
  exprt &range=static_cast<exprt &>(inst.add(ID_range));

  mp_integer msb, lsb;
  
  if(range.is_nil() || range.id()=="")
    msb=lsb=0;
  else
    convert_range(range, msb, lsb);

  if(lsb>msb) std::swap(lsb, msb);
  mp_integer width=msb-lsb+1;
  
  inst.remove(ID_range);

  typet &type=inst.type();
  if(width==1)
    type.id(ID_bool);
  else
  {
    type.id(ID_unsignedbv);
    type.set(ID_width, integer2string(width));
  }

  Forall_operands(o_it, inst)
  {
    convert_expr(*o_it);
    propagate_type(*o_it, type);
  }
}

/*******************************************************************\

Function: verilog_typecheckt::convert_function_or_task

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_function_or_task(verilog_declt &decl)
{
  irep_idt decl_class=decl.get_class();

  const std::string identifier=
    id2string(module_identifier)+"."+
    id2string(decl.get_identifier());

  symbol_tablet::symbolst::iterator result=
    symbol_table.symbols.find(identifier);

  if(result==symbol_table.symbols.end())
  {
    error().source_location=decl.source_location();
    error() << "expected to find " << decl_class << " symbol `"
        << identifier << "' in symbol_table";
    throw 0;
  }
  
  symbolt &symbol=result->second;
  
  decl.set_identifier(symbol.name);

  irept::subt &declarations=decl.declarations();
  
  Forall_irep(it, declarations)
  {
    assert(it->id()==ID_decl);
    convert_decl(static_cast<verilog_declt &>(*it));
  }

  function_or_task_name=symbol.name;
  convert_statement(decl.body());
  function_or_task_name="";
  
  symbol.value=decl.body();
}

/*******************************************************************\

Function: verilog_typecheckt::convert_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheckt::elaborate_const_function_call(
  const function_call_exprt &function_call)
{
  const function_call_exprt::argumentst &arguments=
    function_call.arguments();

  // find the function
  if(function_call.function().id()!=ID_symbol)
  {
    error().source_location=function_call.source_location();
    error() << "expected function symbol, but got `"
            << to_string(function_call.function()) << '\'' << eom;
    throw 0;
  }

  const symbolt &function_symbol=
    ns.lookup(to_symbol_expr(function_call.function()));

  // typecheck it
  verilog_declt decl=to_verilog_decl(function_symbol.value);

  irept::subt &declarations=decl.declarations();

  Forall_irep(it, declarations)
    convert_decl(static_cast<verilog_declt &>(*it));

  function_or_task_name=function_symbol.name;
  convert_statement(decl.body());
  
  const code_typet &code_type=
    to_code_type(function_symbol.type);

  const code_typet::parameterst &parameters=
    code_type.parameters();
    
  if(parameters.size()!=arguments.size())
  {
    error().source_location=function_call.source_location();
    error() << "function call has wrong number of arguments" << eom;
    throw 0;
  }
  
  // elaborate the arguments of the call and assign to parameter
  
  varst old_vars;
  
  for(std::size_t i=0; i<arguments.size(); i++)
  {
    exprt value=elaborate_const_expression(arguments[i]);

    if(!value.is_constant())
    {
      error().source_location=arguments[i].source_location();
      error() << "constant function argument is not constant" << eom;
      throw 0;
    }
    
    irep_idt p_identifier=parameters[i].get_identifier();

    old_vars[p_identifier]=var_value(p_identifier);
    vars[p_identifier]=value;
    
    #if 0
    status() << "ASSIGN " << p_identifier << " <- " << to_string(value) << eom;
    #endif
  }

  // interpret it
  verilog_interpreter(decl.body());

  function_or_task_name="";
  
  // get return value

  exprt return_value=var_value(
    id2string(function_symbol.name)+"."+
    id2string(function_symbol.base_name));

  return return_value;
}

/*******************************************************************\

Function: verilog_typecheckt::convert_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_decl(verilog_declt &decl)
{
  irep_idt decl_class=decl.get_class();

  if(decl_class==ID_function ||
     decl_class==ID_task)
  {
    convert_function_or_task(decl);
    return;
  }
  else if(decl_class==ID_genvar)
  {
    // ignore here
    return;
  }

  Forall_operands(it, decl)
  {
    if(it->id()==ID_symbol)
    {
      // nothing to do
    }
    else if(it->id()==ID_equal)
    {
      if(it->operands().size()!=2)
      {
        error() << "expected two operands in assignment" << eom;
        throw 0;
      }

      exprt &lhs=it->op0();
      exprt &rhs=it->op1();

      if(lhs.id()!=ID_symbol)
      {
        error() << "expected symbol on left hand side of assignment, "
                << " but got `" << to_string(lhs) << "'" << eom;
        throw 0;
      }

      const std::string identifier=
        id2string(module_identifier)+"."+
        lhs.get_string(ID_identifier);

      lhs.set(ID_identifier, identifier);

      symbolt &symbol=symbol_table_lookup(identifier);
      convert_expr(rhs);
      propagate_type(rhs, symbol.type);
      lhs.type()=symbol.type;

      if(symbol.is_state_var)
      {
      }
      else
      {
        if(!symbol.value.is_nil())
        {
          error().source_location=it->source_location();
          error() << "Net " << identifier << " is assigned twice";
          throw 0;
        }
      }
    }
  }
}

/*******************************************************************\

Function: verilog_typecheckt::convert_inst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_inst(verilog_instt &inst)
{
  const irep_idt &inst_module=inst.get_module();

  // must be user-defined

  const irep_idt identifier=
    verilog_module_symbol(id2string(inst_module));

  exprt::operandst &parameter_assignments=
    inst.parameter_assignments();
  
  Forall_expr(it, parameter_assignments)
  {
    // these must be constants
    if(it->id()==ID_named_parameter_assignment)
    {
      mp_integer v_int;
      convert_const_expression(static_cast<exprt &>(it->add(ID_value)), v_int);
      it->add(ID_value)=from_integer(v_int, integer_typet());
    }
    else
    {
      mp_integer v_int;
      convert_const_expression(*it, v_int);
      *it=from_integer(v_int, integer_typet());
    }
  }

  irep_idt new_identifier=
    parameterize_module(
      inst.source_location(),
      identifier,
      parameter_assignments);

  inst.set_module(new_identifier);
  
  // get the instance symbols
  forall_operands(it, inst)
  {
    irep_idt instance_identifier=
      id2string(module_symbol.name)+"."+id2string(it->get(ID_instance));
  
    symbolt &instance_symbol=symbol_table_lookup(instance_identifier);
  
    // fix the module in the instance symbol
    instance_symbol.value.set(ID_module, new_identifier);
  }
  
  const symbolt &parameterized_module_symbol=
    symbol_table_lookup(new_identifier);

  // check the arguments
  Forall_operands(it, inst)
    typecheck_port_connections(*it, parameterized_module_symbol);
}

/*******************************************************************\

Function: verilog_typecheckt::convert_inst_builtin

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_inst_builtin(
  verilog_inst_builtint &inst)
{
  const irep_idt &inst_module=inst.get_module();

  Forall_operands(it, inst)
  {
    exprt &instance=*it;

    typecheck_builtin_port_connections(instance);

    // check built-in ones
    if(inst_module==ID_bufif0 ||
       inst_module==ID_bufif1 ||
       inst_module==ID_notif0 ||
       inst_module==ID_notif1)
    {
    
    }
    else if(inst_module==ID_nmos ||
            inst_module==ID_pmos ||
            inst_module==ID_rnmos ||
            inst_module==ID_rpmos)
    {

    }
    else if(inst_module==ID_and ||
            inst_module==ID_nand ||
            inst_module==ID_or ||
            inst_module==ID_nor ||
            inst_module==ID_xor ||
            inst_module==ID_xnor)
    {
      if(instance.operands().size()<2)
      {
        error().source_location=instance.source_location();
        error() << "Primitive gate " << inst_module
                << " expects at least two operands";
        throw 0;
      }
    }
    else if(inst_module==ID_buf ||
            inst_module==ID_not)
    {
      if(instance.operands().size()<2)
      {
        error().source_location=instance.source_location();
        error() << "Primitive gate " << inst_module
                << " expects at least two operands";
        throw 0;
      }
    }
    else if(inst_module=="tranif0" ||
            inst_module=="tranif1" ||
            inst_module=="rtranif1" ||
            inst_module=="rtranif0")
    {

    }
    else if(inst_module=="tran"  ||
            inst_module=="rtran")
    {

    }
    else
    {
      error().source_location=inst.source_location();
      error() << "Unknown primitive Verilog module "
              << inst_module;
      throw 0;
    }
  }
}

/*******************************************************************\

Function: verilog_typecheckt::convert_always

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_always(
  verilog_alwayst &module_item)
{
  if(module_item.operands().size()!=1)
  {
    error().source_location=module_item.source_location();
    error() << "always statement expected to have one operand" << eom;
    throw 0;
  }

  convert_statement(module_item.statement());
}

/*******************************************************************\

Function: verilog_typecheckt::convert_initial

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_initial(
  verilog_initialt &module_item)
{
  if(module_item.operands().size()!=1)
  {
    error().source_location=module_item.source_location();
    error() << "initial statement expected to have one operand" << eom;
    throw 0;
  }

  convert_statement(module_item.statement());
}

/*******************************************************************\

Function: verilog_typecheckt::convert_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_block(verilog_blockt &statement)
{
  // these may be 'named blocks' with an identifier
  bool is_named=statement.is_named();
  
  if(is_named)
    enter_named_block(statement.get_identifier());

  Forall_operands(it, statement)
    convert_statement(to_verilog_statement(*it));
    
  if(is_named)
    named_blocks.pop_back();
}

/*******************************************************************\

Function: verilog_typecheckt::check_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::check_lhs(
  const exprt &lhs,
  vassignt vassign)
{
  if(lhs.id()==ID_index)
    check_lhs(to_index_expr(lhs).array(), vassign);
  else if(lhs.id()==ID_extractbit)
  {
    if(lhs.operands().size()!=2)
    {
      error() << "extractbit takes two operands" << eom;
      throw 0;
    }

    check_lhs(lhs.op0(), vassign);
  }
  else if(lhs.id()==ID_extractbits)
  {
    if(lhs.operands().size()!=3)
    {
      error() << "extractbits takes three operands" << eom;
      throw 0;
    }

    check_lhs(lhs.op0(), vassign);
  }
  else if(lhs.id()==ID_concatenation)
  {
    forall_operands(it, lhs)
      check_lhs(*it, vassign);

    return;
  }
  else if(lhs.id()==ID_symbol)
  {
    // get identifier

    irep_idt identifier=
      to_symbol_expr(lhs).get_identifier();

    const symbolt &symbol=lookup(identifier);

    switch(vassign)
    {
    case A_CONTINUOUS:
      if(symbol.is_state_var)
      {
        error().source_location=lhs.source_location();
        error() << "continuous assignment to register" << eom;
        throw 0;
      }
      else if(symbol.is_input && !symbol.is_output)
      {
        error().source_location=lhs.source_location();
        error() << "continuous assignment to input" << eom;
        throw 0;
      }
      break;

    case A_BLOCKING:
    case A_NON_BLOCKING:
      if(!symbol.is_state_var &&
         !symbol.is_lvalue)
      {
        error().source_location=lhs.source_location();
        error() << "assignment to non-register" << eom;
        throw 0;
      }

      break;
    }
  }
  else
  {
    error() << "typechecking: failed to get identifier on LHS" << eom;
    throw 0;
  }
}

/*******************************************************************\

Function: verilog_typecheckt::convert_procedural_continuous_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_procedural_continuous_assign(
  verilog_procedural_continuous_assignt &statement)
{
  // down and up again
  convert_continuous_assign(
    static_cast<verilog_continuous_assignt &>(
      static_cast<exprt &>(statement)));
}

/*******************************************************************\

Function: verilog_typecheckt::convert_continuous_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_continuous_assign(
  verilog_continuous_assignt &module_item)
{
  Forall_operands(it, module_item)
  {
    if(it->id()!=ID_equal || it->operands().size()!=2)
    {
      error().source_location=it->source_location();
      error() << "malformed continuous assignment" << eom;
      throw 0;
    }

    it->type()=bool_typet();

    exprt &lhs=it->op0();
    exprt &rhs=it->op1();

    convert_expr(lhs);
    convert_expr(rhs);
    propagate_type(rhs, lhs.type());

    check_lhs(lhs, A_CONTINUOUS);
  }
}

/*******************************************************************\

Function: verilog_typecheckt::convert_function_call_or_task_enable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_function_call_or_task_enable(
  verilog_function_callt &statement)
{
  irep_idt base_name=
    to_symbol_expr(statement.function()).get_identifier();

  // We ignore everyting that starts with a '$',
  // e.g., $display etc

  if(!base_name.empty() && base_name[0]=='$')
  {
  }
  else
  {
    // look it up
    const irep_idt identifier=
      id2string(module_identifier)+"."+
      id2string(base_name);
    
    const symbolt &symbol=lookup(identifier);

    if(symbol.type.id()!=ID_code)
    {
      error().source_location=statement.source_location();
      error() << "expected task or function name" << eom;
      throw 0;
    }
    
    const code_typet &code_type=to_code_type(symbol.type);
    
    // check arguments
    const code_typet::parameterst &parameter_types=code_type.parameters();
    exprt::operandst &arguments=statement.arguments();
    
    if(parameter_types.size()!=arguments.size())
    {
      error().source_location=statement.source_location();
      error() << "wrong number of arguments" << eom;
      throw 0;
    }

    for(unsigned i=0; i<arguments.size(); i++)
    {
      convert_expr(arguments[i]);
      propagate_type(arguments[i], parameter_types[i].type());
    }
    
    statement.function().type()=symbol.type;
    statement.function().set(ID_identifier, symbol.name);
  }
}

/*******************************************************************\

Function: verilog_typecheckt::convert_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_assign(
  verilog_assignt &statement,
  bool blocking)
{
  if(statement.operands().size()!=2)
  {
    error().source_location=statement.source_location();
    error() << "assign statement expected to have two operands" << eom;
    throw 0;
  }

  exprt &lhs=statement.op0();
  exprt &rhs=statement.op1();

  convert_expr(lhs);
  convert_expr(rhs);
  propagate_type(rhs, lhs.type());
  check_lhs(lhs, blocking?A_BLOCKING:A_NON_BLOCKING);
}

/*******************************************************************\

Function: verilog_typecheckt::convert_assert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_assert(exprt &statement)
{
  if(statement.operands().size()!=2)
  {
    error().source_location=statement.source_location();
    error() << "assert statement expected to have two operands" << eom;
    return;
  }
  
  exprt &cond=statement.op0();

  convert_expr(cond);
  make_boolean(cond);
  
  // There is an implicit 'always'
  exprt property;
  
  if(cond.id()==ID_sva_always)
    property=cond;
  else
    property=unary_predicate_exprt(ID_sva_always, cond);
  
  assertion_counter++;
  
  const irep_idt &identifier=statement.get(ID_identifier);
  
  irep_idt base_name;
  
  if(identifier=="")
    base_name=i2string(assertion_counter);
  else
    base_name=identifier;
  
  std::string full_identifier=
    id2string(module_identifier)+
    ".property."+id2string(base_name);

  if(symbol_table.symbols.find(full_identifier)!=
     symbol_table.symbols.end())
  {
    error().source_location=statement.source_location();
    error() << "property identifier `" << base_name
            << "' already used" << eom;
    return; // continue with error
  }

  statement.set(ID_identifier, full_identifier);

  symbolt symbol;

  symbol.mode=mode;
  symbol.module=module_identifier;
  symbol.value.swap(property);
  symbol.base_name=base_name;
  symbol.name=full_identifier;
  symbol.type=bool_typet();
  symbol.is_property=true;
  symbol.location=statement.find_source_location();
  symbol.pretty_name=strip_verilog_prefix(full_identifier);

  symbolt *new_symbol;
  symbol_table.move(symbol, new_symbol);
}

/*******************************************************************\

Function: verilog_typecheckt::convert_assume

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_assume(exprt &statement)
{
  if(statement.operands().size()!=2)
  {
    error().source_location=statement.source_location();
    error() << "assume statement expected to have two operands" << eom;
    return;
  }
  
  exprt &cond=statement.op0();

  convert_expr(cond);
  make_boolean(cond);
}

/*******************************************************************\

Function: verilog_typecheckt::convert_case_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_case_values(
  exprt &values,
  const exprt &case_operand)
{
  if(values.id()==ID_default)
    return;

  Forall_operands(it, values)
  {
    convert_expr(*it);
    typet t=max_type(it->type(), case_operand.type());
    propagate_type(*it, t);
  }
}

/*******************************************************************\

Function: verilog_typecheckt::convert_case

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_case(
  verilog_case_baset &statement)
{
  if(statement.operands().size()<1)
  {
    error().source_location=statement.source_location();
    error() << "case statement expected to have at least one operand" << eom;
    throw 0;
  }

  exprt &case_operand=statement.case_operand();

  convert_expr(case_operand);

  for(unsigned i=1; i<statement.operands().size(); i++)
  {
    verilog_case_itemt &e=
      to_verilog_case_item(statement.operands()[i]);

    convert_case_values(e.case_value(), case_operand);
    convert_statement(e.case_statement());
  }
}

/*******************************************************************\

Function: verilog_typecheckt::convert_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_if(verilog_ift &statement)
{
  if(statement.operands().size()!=2 &&
     statement.operands().size()!=3)
  {
    error().source_location=statement.source_location();
    error() << "if statement expected to have two or three operands" << eom;
    throw 0;
  }

  exprt &condition=statement.condition();

  convert_expr(condition);
  make_boolean(condition);

  convert_statement(statement.true_case());

  if(statement.operands().size()==3)
    convert_statement(statement.false_case());
}

/*******************************************************************\

Function: verilog_typecheckt::convert_event_guard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_event_guard(
  verilog_event_guardt &statement)
{
  if(statement.operands().size()!=2)
  {
    error().source_location=statement.source_location();
    error() << "event_guard expected to have two operands" << eom;
    throw 0;
  }

  exprt &guard=statement.guard();

  convert_expr(guard);
  make_boolean(guard);

  convert_statement(statement.body());
}

/*******************************************************************\

Function: verilog_typecheckt::convert_delay

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_delay(verilog_delayt &statement)
{
  if(statement.operands().size()!=2)
  {
    error().source_location=statement.source_location();
    error() << "delay expected to have two operands" << eom;
    throw 0;
  }

  convert_statement(statement.body());
}

/*******************************************************************\

Function: verilog_typecheckt::convert_for

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_for(verilog_fort &statement)
{
  if(statement.operands().size()!=4)
  {
    error().source_location=statement.source_location();
    error() << "for expected to have four operands" << eom;
    throw 0;
  }

  convert_statement(statement.initialization());

  exprt &condition=statement.condition();
  convert_expr(condition);
  make_boolean(condition);

  convert_statement(statement.inc_statement());
  convert_statement(statement.body());
}

/*******************************************************************\

Function: verilog_typecheckt::convert_prepostincdec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_prepostincdec(verilog_statementt &statement)
{
  if(statement.operands().size()!=1)
  {
    error().source_location=statement.source_location();
    throw statement.id_string()+" expected to have one operand";
  }

  convert_expr(statement.op0());
}

/*******************************************************************\

Function: verilog_typecheckt::convert_while

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_while(
  verilog_whilet &statement)
{
  if(statement.operands().size()!=2)
  {
    error().source_location=statement.source_location();
    error() << "while expected to have two operands" << eom;
    throw 0;
  }

  exprt &condition=statement.condition();
  convert_expr(condition);
  make_boolean(condition);

  convert_statement(statement.body());
}

/*******************************************************************\

Function: verilog_typecheckt::convert_repeat

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_repeat(
  verilog_repeatt &statement)
{
  if(statement.operands().size()!=2)
  {
    error().source_location=statement.source_location();
    error() << "repeat expected to have two operands" << eom;
    throw 0;
  }

  exprt &condition=statement.condition();
  convert_expr(condition);
  make_boolean(condition);

  convert_statement(statement.body());
}

/*******************************************************************\

Function: verilog_typecheckt::convert_forever

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_forever(
  verilog_forevert &statement)
{
  if(statement.operands().size()!=1)
  {
    error().source_location=statement.source_location();
    error() << "forever expected to have one operand" << eom;
    throw 0;
  }

  convert_statement(statement.body());
}

/*******************************************************************\

Function: verilog_typecheckt::convert_statement

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_statement(
  verilog_statementt &statement)
{
  if(statement.id()==ID_block)
    convert_block(to_verilog_block(statement));
  else if(statement.id()==ID_case ||
          statement.id()==ID_casex ||
          statement.id()==ID_casez)
    convert_case(to_verilog_case_base(statement));
  else if(statement.id()==ID_blocking_assign)
    convert_assign(to_verilog_assign(statement), true);
  else if(statement.id()==ID_continuous_assign)
    convert_procedural_continuous_assign(
      to_verilog_procedural_continuous_assign(statement));
  else if(statement.id()==ID_assert)
    convert_assert(statement);
  else if(statement.id()==ID_assume)
    convert_assume(statement);
  else if(statement.id()==ID_non_blocking_assign)
    convert_assign(to_verilog_assign(statement), false);
  else if(statement.id()==ID_if)
    convert_if(to_verilog_if(statement));
  else if(statement.id()==ID_event_guard)
    convert_event_guard(to_verilog_event_guard(statement));
  else if(statement.id()==ID_delay)
    convert_delay(to_verilog_delay(statement));
  else if(statement.id()==ID_for)
    convert_for(to_verilog_for(statement));
  else if(statement.id()==ID_while)
    convert_while(to_verilog_while(statement));
  else if(statement.id()==ID_repeat)
    convert_repeat(to_verilog_repeat(statement));
  else if(statement.id()==ID_forever)
    convert_forever(to_verilog_forever(statement));
  else if(statement.id()==ID_skip)
  {
    // do nothing
  }
  else if(statement.id()==ID_preincrement ||
          statement.id()==ID_predecrement ||
          statement.id()==ID_postincrement ||
          statement.id()==ID_postdecrement)
    convert_prepostincdec(statement);
  else if(statement.id()==ID_function_call)
    convert_function_call_or_task_enable(to_verilog_function_call(statement));
  else if(statement.id()==ID_decl)
    convert_decl(to_verilog_decl(statement));
  else
  {
    error().source_location=statement.source_location();
    error() << "unexpected statement:" << statement.id() << eom;
    throw 0;
  }
}

/*******************************************************************\

Function: verilog_typecheckt::convert_module_item

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_module_item(
  verilog_module_itemt &module_item)
{
  if(module_item.id()==ID_specify)
  {
  }
  else if(module_item.id()==ID_decl)
    convert_decl(to_verilog_decl(module_item));
  else if(module_item.id()==ID_parameter_decl ||
          module_item.id()==ID_local_parameter_decl)
  {
  }
  else if(module_item.id()==ID_always)
    convert_always(to_verilog_always(module_item));
  else if(module_item.id()==ID_assert)
    convert_assert(module_item);
  else if(module_item.id()==ID_assume)
    convert_assume(module_item);
  else if(module_item.id()==ID_initial)
    convert_initial(to_verilog_initial(module_item));
  else if(module_item.id()==ID_continuous_assign)
    convert_continuous_assign(to_verilog_continuous_assign(module_item));
  else if(module_item.id()==ID_inst)
    convert_inst(to_verilog_inst(module_item));
  else if(module_item.id()==ID_inst_builtin)
    convert_inst_builtin(to_verilog_inst_builtin(module_item));
  else if(module_item.id()==ID_generate_block)
  {
    // should be gone already
    error().source_location=module_item.source_location();
    error() << "unexpected generate_block module item" << eom;
    throw 0;
  }
  else if(module_item.id()=="set_genvars")
  {
    genvars.clear();
    const irept &variables=module_item.find("variables");
    forall_named_irep(it, variables.get_named_sub())
      genvars[name2string(it->first)]=
        string2integer(it->second.id_string());
      
    if(module_item.operands().size()!=1)
    {
      error() << "set_genvars expects one operand" << eom;
      throw 0;
    }
      
    exprt tmp;
    tmp.swap(module_item.op0());
    module_item.swap(tmp);
    convert_module_item(module_item);
  }
  else
  {
    error().source_location=module_item.source_location();
    error() << "unexpected module item:" << module_item.id() << eom;
    throw 0;
  }
}

/*******************************************************************\

Function: verilog_typecheckt::convert_statements

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_statements()
{
  exprt &value=module_symbol.value;
  
  value.id(ID_verilog_module);

  const irept &module_source=
    module_symbol.type.find(ID_module_source);

  const irept &module_items=module_source.find(ID_module_items);

  value.reserve_operands(module_items.get_sub().size());

  // do the generate stuff

  forall_irep(it, module_items.get_sub())
    elaborate_generate_item(
      static_cast<const exprt &>(*it), value.operands());

  // typecheck
  
  Forall_operands(it, value)
    convert_module_item(static_cast<verilog_module_itemt &>(*it));
}

/*******************************************************************\

Function: verilog_typecheckt::implicit_wire

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_typecheckt::implicit_wire(
  const irep_idt &identifier,
  const symbolt *&symbol_ptr)
{
  std::string full_identifier=
    id2string(module_identifier)+"."+id2string(identifier);

  symbolt symbol;

  symbol.mode=mode;
  symbol.module=module_identifier;
  symbol.value.make_nil();
  symbol.base_name=identifier;
  symbol.name=full_identifier;
  symbol.type=bool_typet(); // TODO: other types?

  symbolt *new_symbol;
  symbol_table.move(symbol, new_symbol);
  symbol_ptr=new_symbol;

  return false;
}

/*******************************************************************\

Function: verilog_typecheckt::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::typecheck()
{
  module_interface();
  convert_statements();
}

/*******************************************************************\

Function: verilog_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_typecheck(
  const verilog_parse_treet &parse_tree,
  symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  verilog_parse_treet::module_mapt::const_iterator it=
    parse_tree.module_map.find(
      id2string(verilog_module_name(module)));
    
  if(it==parse_tree.module_map.end())
  {
    messaget message(message_handler);
    message.error() << "module `" << module 
                    << "' not found" << messaget::eom;
    return true;
  }

  return verilog_typecheck(
    symbol_table, it->second->verilog_module, message_handler);
}

/*******************************************************************\

Function: verilog_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_typecheck(
  symbol_tablet &symbol_table,
  const verilog_modulet &verilog_module,
  message_handlert &message_handler)
{
  // create symbol

  symbolt symbol;

  symbol.mode=ID_Verilog;
  symbol.base_name=verilog_module.name;
  symbol.type=module_typet();
  symbol.name=verilog_module_symbol(verilog_module.name);
  symbol.base_name=verilog_module.name;
  symbol.pretty_name=verilog_module.name;
  symbol.module=symbol.name;
  symbol.location=verilog_module.location;

  symbol.type.add(ID_module_source)=verilog_module.to_irep();
  
  // put symbol in symbol_table

  symbolt *new_symbol;

  if(symbol_table.move(symbol, new_symbol))
  {
    messaget message(message_handler);
    message.error() << "duplicate definition of module " 
                    << symbol.base_name << messaget::eom;
    throw 0;
  }

  verilog_typecheckt verilog_typecheck(*new_symbol, symbol_table, message_handler);
  return verilog_typecheck.typecheck_main();
}
