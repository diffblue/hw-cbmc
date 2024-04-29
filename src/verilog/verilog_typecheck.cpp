/*******************************************************************\

Module: Verilog Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_typecheck.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/ebmc_util.h>
#include <util/expr_util.h>
#include <util/mathematical_types.h>
#include <util/replace_symbol.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include "expr2verilog.h"
#include "verilog_expr.h"
#include "verilog_types.h"

#include <cassert>
#include <map>
#include <set>

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
    ns.lookup(port.get(ID_identifier));

  if(!symbol.is_input && !symbol.is_output)
  {
    throw errort().with_location(op.source_location())
      << "port `" << symbol.name << "' is neither input nor output";
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
  verilog_inst_baset::instancet &inst,
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
  if(
    ports.size() == 0 && inst.connections().size() == 1 &&
    inst.connections().front().is_nil())
  {
    inst.connections().clear();
  }

  if(inst.connections().empty())
  {
    if(!ports.empty())
    {
      throw errort().with_location(inst.source_location())
        << "module does not have ports";
    }

    return;
  }

  // named port connection?

  if(inst.connections().front().id() == ID_named_port_connection)
  {
    // We don't require that all ports are connected.
  
    std::set<irep_idt> assigned_ports;

    for(auto &connection : inst.connections())
    {
      if(connection.id() != ID_named_port_connection)
      {
        throw errort().with_location(inst.source_location())
          << "expected a named port connection";
      }

      auto &named_port_connection =
        to_verilog_named_port_connection(connection);

      exprt &value = named_port_connection.value();
      const irep_idt &name = named_port_connection.port().get(ID_identifier);

      bool found=false;

      std::string identifier=
        id2string(symbol.module)+"."+id2string(name);

      named_port_connection.port().set(ID_identifier, identifier);

      if(assigned_ports.find(name)!=
         assigned_ports.end())
      {
        throw errort().with_location(connection.source_location())
          << "port name " << name << " assigned twice";
      }

      for(auto &port : ports)
      {
        if(port.get(ID_identifier) == identifier)
        {
          auto &p_expr = static_cast<const exprt &>(port);
          found=true;
          typecheck_port_connection(value, p_expr);
          named_port_connection.port().type() = p_expr.type();
          break;
        }
      }

      if(!found)
      {
        throw errort().with_location(connection.source_location())
          << "port name " << identifier << " not found";
      }

      assigned_ports.insert(identifier);
    }
  }
  else // just a list without names
  {
    if(inst.connections().size() != ports.size())
    {
      throw errort().with_location(inst.source_location())
        << "wrong number of arguments: expected " << ports.size() << " but got "
        << inst.connections().size();
    }

    irept::subt::const_iterator p_it=
      ports.begin();

    for(auto &connection : inst.connections())
    {
      typecheck_port_connection(connection, (exprt &)*p_it);
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
  verilog_inst_baset::instancet &inst)
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

  for(auto &connection : inst.connections())
  {
    convert_expr(connection);
    propagate_type(connection, type);
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

  auto result=symbol_table.get_writeable(identifier);

  if(result==nullptr)
  {
    throw errort().with_location(decl.source_location())
      << "expected to find " << decl_class << " symbol `" << identifier
      << "' in symbol_table";
  }
  
  symbolt &symbol=*result;
  
  decl.set_identifier(symbol.name);

  function_or_task_name = symbol.name;

  for(auto &inner_decl : decl.declarations())
    convert_decl(inner_decl);

  convert_statement(decl.body());

  function_or_task_name="";
  
  symbol.value=decl.body();
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_constant_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheckt::elaborate_constant_function_call(
  const function_call_exprt &function_call)
{
  const function_call_exprt::argumentst &arguments=
    function_call.arguments();

  // find the function
  if(function_call.function().id()!=ID_symbol)
  {
    throw errort().with_location(function_call.source_location())
      << "expected function symbol, but got `"
      << to_string(function_call.function()) << '\'';
  }

  const symbolt &function_symbol=
    ns.lookup(to_symbol_expr(function_call.function()));

  // typecheck it
  verilog_declt decl=to_verilog_decl(function_symbol.value);

  function_or_task_name = function_symbol.name;

  for(auto &inner_decl : decl.declarations())
    convert_decl(inner_decl);

  convert_statement(decl.body());
  
  const code_typet &code_type=
    to_code_type(function_symbol.type);

  const code_typet::parameterst &parameters=
    code_type.parameters();
    
  if(parameters.size()!=arguments.size())
  {
    throw errort().with_location(function_call.source_location())
      << "function call has wrong number of arguments";
  }
  
  // elaborate the arguments of the call and assign to parameter
  
  varst old_vars;
  
  for(std::size_t i=0; i<arguments.size(); i++)
  {
    exprt value = elaborate_constant_expression(arguments[i]);

    if(!value.is_constant())
    {
      throw errort().with_location(arguments[i].source_location())
        << "constant function argument is not constant";
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
  else if(decl_class == ID_verilog_genvar)
  {
    // ignore here
    return;
  }

  for(auto &declarator : decl.declarators())
  {
    DATA_INVARIANT(declarator.id() == ID_declarator, "must have declarator");

    // in a named block?
    irep_idt named_block;
    if(!named_blocks.empty())
      named_block = named_blocks.back();

    // fix the type and identifier
    irep_idt full_identifier;

    if(!function_or_task_name.empty())
      full_identifier = id2string(function_or_task_name) + "." +
                        id2string(named_block) +
                        id2string(declarator.base_name());
    else
      full_identifier = id2string(module_identifier) + "." +
                        id2string(named_block) +
                        id2string(declarator.base_name());

    symbolt &symbol = symbol_table_lookup(full_identifier);
    declarator.type() = symbol.type;

    declarator.identifier(full_identifier);

    if(declarator.has_value())
    {
      auto &rhs = declarator.value();
      convert_expr(rhs);
      propagate_type(rhs, symbol.type);
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

  // The instantiated module must be user-defined.

  const irep_idt module_identifier =
    verilog_module_symbol(id2string(inst_module));

  exprt::operandst &parameter_assignments=
    inst.parameter_assignments();

  Forall_expr(it, parameter_assignments)
  {
    // These must be constants. Preserve the location.
    if(it->id()==ID_named_parameter_assignment)
    {
      auto &value = static_cast<exprt &>(it->add(ID_value));
      mp_integer v_int = convert_integer_constant_expression(value);
      value =
        from_integer(v_int, integer_typet()).with_source_location<exprt>(*it);
    }
    else
    {
      mp_integer v_int = convert_integer_constant_expression(*it);
      *it =
        from_integer(v_int, integer_typet()).with_source_location<exprt>(*it);
    }
  }

  // get the instance symbols
  for(auto &instance : inst.instances())
  {
    const auto instance_base_name = instance.base_name();

    const irep_idt instance_identifier =
      hierarchical_identifier(instance_base_name);

    instance.identifier(instance_identifier);

    // add relevant defparam assignments
    auto &instance_defparams = defparams[instance_identifier];

    irep_idt new_module_identifier = parameterize_module(
      inst.source_location(),
      module_identifier,
      parameter_assignments,
      instance_defparams);

    inst.set_module(new_module_identifier);

    symbolt &instance_symbol=symbol_table_lookup(instance_identifier);
  
    // fix the module in the instance symbol
    instance_symbol.value.set(ID_module, new_module_identifier);

    const symbolt &parameterized_module_symbol =
      symbol_table_lookup(new_module_identifier);

    // check the port connections
    typecheck_port_connections(instance, parameterized_module_symbol);
  }
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

  for(auto &instance : inst.instances())
  {
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
      if(instance.connections().size() < 2)
      {
        throw errort().with_location(instance.source_location())
          << "Primitive gate " << inst_module
          << " expects at least two operands";
      }
    }
    else if(inst_module==ID_buf ||
            inst_module==ID_not)
    {
      if(instance.connections().size() < 2)
      {
        throw errort().with_location(instance.source_location())
          << "Primitive gate " << inst_module
          << " expects at least two operands";
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
      throw errort().with_location(inst.source_location())
        << "Unknown primitive Verilog module " << inst_module;
    }
  }
}

/*******************************************************************\

Function: verilog_typecheckt::convert_always_base

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_always_base(verilog_always_baset &module_item)
{
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
    throw errort().with_location(module_item.source_location())
      << "initial statement expected to have one operand";
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
    enter_named_block(statement.base_name());

  for(auto &block_statement : statement.statements())
    convert_statement(block_statement);

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
  {
    check_lhs(to_index_expr(lhs).array(), vassign);
  }
  else if(lhs.id()==ID_extractbit)
  {
    if(lhs.operands().size()!=2)
    {
      throw errort() << "extractbit takes two operands";
    }

    check_lhs(to_extractbit_expr(lhs).src(), vassign);
  }
  else if(lhs.id()==ID_extractbits)
  {
    if(lhs.operands().size()!=3)
    {
      throw errort() << "extractbits takes three operands";
    }

    check_lhs(to_extractbits_expr(lhs).src(), vassign);
  }
  else if(lhs.id()==ID_concatenation)
  {
    forall_operands(it, lhs)
      check_lhs(*it, vassign);

    return;
  }
  else if(lhs.id()==ID_symbol)
  {
    const symbolt &symbol=ns.lookup(to_symbol_expr(lhs));

    switch(vassign)
    {
    case A_CONTINUOUS:
      if(symbol.is_state_var)
      {
        // Continuous assignments can drive variables.
      }
      else if(symbol.is_input && !symbol.is_output)
      {
        throw errort().with_location(lhs.source_location())
          << "continuous assignment to input";
      }
      break;

    case A_BLOCKING:
    case A_NON_BLOCKING:
      if(!symbol.is_state_var &&
         !symbol.is_lvalue)
      {
        throw errort().with_location(lhs.source_location())
          << "procedural assignment to a net\n"
          << "Identifier " << symbol.display_name() << " is declared as "
          << to_string(symbol.type) << " on line " << symbol.location.get_line()
          << '.';
      }
      break;

    case A_PROCEDURAL_CONTINUOUS:
      if(!symbol.is_state_var && !symbol.is_lvalue)
      {
        throw errort().with_location(lhs.source_location())
          << "procedural continuous assignment to a net\n"
          << "Identifier " << symbol.display_name() << " is declared as "
          << to_string(symbol.type) << " on line " << symbol.location.get_line()
          << '.';
      }
      break;
    }
  }
  else if(lhs.id() == ID_member)
  {
    check_lhs(to_member_expr(lhs).struct_op(), vassign);
  }
  else
  {
    throw errort() << "typechecking: failed to get identifier on LHS "
                   << lhs.pretty();
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
  // On path to deprecation.
  for(auto &assignment : statement.operands())
  {
    if(assignment.id() != ID_equal || assignment.operands().size() != 2)
    {
      throw errort().with_location(assignment.source_location())
        << "malformed procedural continuous assignment";
    }

    assignment.type() = bool_typet();

    exprt &lhs = to_binary_expr(assignment).lhs();
    exprt &rhs = to_binary_expr(assignment).rhs();

    convert_expr(lhs);
    convert_expr(rhs);

    propagate_type(rhs, lhs.type());

    check_lhs(lhs, A_PROCEDURAL_CONTINUOUS);
  }
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
      throw errort().with_location(it->source_location())
        << "malformed continuous assignment";
    }

    it->type()=bool_typet();

    exprt &lhs = to_binary_expr(*it).lhs();
    exprt &rhs = to_binary_expr(*it).rhs();

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
    
    const symbolt &symbol=ns.lookup(identifier);

    if(symbol.type.id()!=ID_code)
    {
      throw errort().with_location(statement.source_location())
        << "expected task or function name";
    }
    
    const code_typet &code_type=to_code_type(symbol.type);
    
    // check arguments
    const code_typet::parameterst &parameter_types=code_type.parameters();
    exprt::operandst &arguments=statement.arguments();
    
    if(parameter_types.size()!=arguments.size())
    {
      throw errort().with_location(statement.source_location())
        << "wrong number of arguments";
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

Function: verilog_typecheckt::convert_paramter_override

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_parameter_override(
  const verilog_parameter_overridet &module_item)
{
  for(auto &assignment : module_item.assignments())
  {
    // Copy the lhs/rhs.
    exprt lhs = to_binary_expr(assignment).lhs();
    exprt rhs = to_binary_expr(assignment).rhs();

    // The lhs is a sequence of module instance names using
    // hierarchical_identifier expressions.
    convert_expr(lhs);

    // turn into identifier
    if(lhs.id() != ID_hierarchical_identifier)
    {
      throw errort().with_location(module_item.source_location())
        << "defparam expected to have a hierachical identifier";
    }

    const auto &hierarchical_identifier = to_hierarchical_identifier_expr(lhs);

    if(hierarchical_identifier.module().id() != ID_symbol)
    {
      throw errort().with_location(module_item.source_location())
        << "defparam expected to have a single level identifier";
    }

    auto module_instance =
      to_symbol_expr(hierarchical_identifier.module()).get_identifier();
    auto parameter_name = hierarchical_identifier.item().get_identifier();

    // The rhs must be a constant at this point.
    auto rhs_value =
      from_integer(convert_integer_constant_expression(rhs), integer_typet());

    // store the assignment
    defparams[module_instance][parameter_name] = rhs_value;
  }
}

/*******************************************************************\

Function: verilog_typecheckt::convert_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_force(verilog_forcet &statement)
{
  exprt &lhs=statement.lhs();
  exprt &rhs=statement.rhs();

  convert_expr(lhs);
  convert_expr(rhs);
  propagate_type(rhs, lhs.type());
  //check_lhs(lhs, blocking?A_BLOCKING:A_NON_BLOCKING);
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
    throw errort().with_location(statement.source_location())
      << "assign statement expected to have two operands";
  }

  exprt &lhs = to_binary_expr(statement).lhs();
  exprt &rhs = to_binary_expr(statement).rhs();

  convert_expr(lhs);
  convert_expr(rhs);
  propagate_type(rhs, lhs.type());
  check_lhs(lhs, blocking?A_BLOCKING:A_NON_BLOCKING);
}

/*******************************************************************\

Function: verilog_typecheckt::convert_assert_assume_cover

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_assert_assume_cover(
  verilog_assert_assume_cover_module_itemt &module_item)
{
  exprt &cond = module_item.condition();

  convert_expr(cond);
  make_boolean(cond);

  if(
    module_item.id() == ID_verilog_assert_property ||
    module_item.id() == ID_verilog_cover_property)
  {
    // We create a symbol for the property.
    // The 'value' of the symbol is set by synthesis.
    const irep_idt &identifier = module_item.identifier();

    irep_idt base_name;

    if(identifier == irep_idt())
    {
      assertion_counter++;
      base_name = std::to_string(assertion_counter);
    }
    else
      base_name = identifier;

    std::string full_identifier =
      id2string(module_identifier) + ".property." + id2string(base_name);

    if(symbol_table.symbols.find(full_identifier) != symbol_table.symbols.end())
    {
      throw errort().with_location(module_item.source_location())
        << "property identifier `" << base_name << "' already used";
    }

    module_item.identifier(full_identifier);

    symbolt symbol{base_name, bool_typet{}, mode};

    symbol.module = module_identifier;
    symbol.value = nil_exprt{}; // set by synthesis
    symbol.name = full_identifier;
    symbol.is_property = true;
    symbol.location = module_item.find_source_location();
    symbol.pretty_name = strip_verilog_prefix(full_identifier);

    symbol_table.insert(std::move(symbol));
  }
}

/*******************************************************************\

Function: verilog_typecheckt::convert_assert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_assert(verilog_assert_statementt &statement)
{
  exprt &cond = statement.condition();

  convert_expr(cond);
  make_boolean(cond);

  // We create a symbol for the property.
  // The 'value' is set by synthesis.
  const irep_idt &identifier = statement.identifier();

  irep_idt base_name;

  if(identifier == irep_idt())
  {
    assertion_counter++;
    base_name = std::to_string(assertion_counter);
  }
  else
    base_name = identifier;

  std::string full_identifier =
    id2string(module_identifier) + ".property." + id2string(base_name);

  if(symbol_table.symbols.find(full_identifier) != symbol_table.symbols.end())
  {
    throw errort().with_location(statement.source_location())
      << "property identifier `" << base_name << "' already used";
  }

  statement.identifier(full_identifier);

  symbolt symbol{base_name, bool_typet{}, mode};

  symbol.module = module_identifier;
  symbol.value = nil_exprt{}; // set by synthesis
  symbol.name = full_identifier;
  symbol.is_property = true;
  symbol.location = statement.find_source_location();
  symbol.pretty_name = strip_verilog_prefix(full_identifier);

  symbolt *new_symbol;
  symbol_table.move(symbol, new_symbol);
}

/*******************************************************************\

Function: verilog_typecheckt::convert_assume

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_assume(verilog_assume_statementt &statement)
{
  exprt &cond = statement.condition();

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
    throw errort().with_location(statement.source_location())
      << "case statement expected to have at least one operand";
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
  exprt &condition = statement.cond();

  convert_expr(condition);
  make_boolean(condition);

  convert_statement(statement.then_case());

  if(statement.has_else_case())
    convert_statement(statement.else_case());
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
    throw errort().with_location(statement.source_location())
      << "event_guard expected to have two operands";
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
    throw errort().with_location(statement.source_location())
      << "delay expected to have two operands";
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
    throw errort().with_location(statement.source_location())
      << "for expected to have four operands";
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
    throw errort().with_location(statement.source_location())
      << statement.id() << " expected to have one operand";
  }

  convert_expr(to_unary_expr(statement).op());
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
    throw errort().with_location(statement.source_location())
      << "while expected to have two operands";
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
    throw errort().with_location(statement.source_location())
      << "repeat expected to have two operands";
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
    throw errort().with_location(statement.source_location())
      << "forever expected to have one operand";
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
  else if(statement.id() == ID_procedural_continuous_assign)
    convert_procedural_continuous_assign(
      to_verilog_procedural_continuous_assign(statement));
  else if(
    statement.id() == ID_assert ||
    statement.id() == ID_verilog_assert_property ||
    statement.id() == ID_verilog_smv_assert)
    convert_assert(to_verilog_assert_statement(statement));
  else if(
    statement.id() == ID_assume ||
    statement.id() == ID_verilog_assume_property ||
    statement.id() == ID_verilog_smv_assume)
    convert_assume(to_verilog_assume_statement(statement));
  else if(statement.id() == ID_verilog_cover_property)
  {
  }
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
  else if(statement.id()==ID_force)
    convert_force(to_verilog_force(statement));
  else if(statement.id() == ID_verilog_label_statement)
    convert_statement(to_verilog_label_statement(statement).statement());
  else if(statement.id() == ID_wait)
  {
  }
  else
  {
    throw errort().with_location(statement.source_location())
      << "unexpected statement: " << statement.id();
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
  else if(module_item.id() == ID_parameter_override)
  {
    // done already
  }
  else if(
    module_item.id() == ID_verilog_always ||
    module_item.id() == ID_verilog_always_comb ||
    module_item.id() == ID_verilog_always_ff ||
    module_item.id() == ID_verilog_always_latch)
  {
    convert_always_base(to_verilog_always_base(module_item));
  }
  else if(
    module_item.id() == ID_verilog_assert_property ||
    module_item.id() == ID_verilog_assume_property ||
    module_item.id() == ID_verilog_cover_property)
  {
    convert_assert_assume_cover(
      to_verilog_assert_assume_cover_module_item(module_item));
  }
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
    // these introduce a scope, much like a named block
    auto &generate_block = to_verilog_generate_block(module_item);
    bool is_named = generate_block.is_named();

    if(is_named)
      enter_named_block(generate_block.base_name());

    for(auto &sub_module_item : generate_block.module_items())
      convert_module_item(sub_module_item);

    if(is_named)
      named_blocks.pop_back();
  }
  else if(module_item.id() == ID_set_genvars)
  {
    genvars.clear();
    const auto &variables = to_verilog_set_genvars(module_item).variables();
    for(auto &var : variables)
      genvars[id2string(var.first)] = string2integer(var.second.id_string());

    if(module_item.operands().size()!=1)
    {
      throw errort() << "set_genvars expects one operand";
    }
      
    exprt tmp;
    tmp.swap(to_unary_expr(module_item).op());
    module_item.swap(tmp);
    convert_module_item(module_item);
  }
  else if(module_item.id() == ID_verilog_final)
  {
  }
  else if(module_item.id() == ID_verilog_let)
  {
    // done already
  }
  else if(module_item.id() == ID_verilog_empty_item)
  {
  }
  else if(module_item.id() == ID_verilog_smv_using)
  {
  }
  else if(module_item.id() == ID_verilog_smv_assume)
  {
  }
  else if(module_item.id() == ID_verilog_package_import)
  {
  }
  else if(module_item.id() == ID_verilog_covergroup)
  {
  }
  else
  {
    throw errort().with_location(module_item.source_location())
      << "unexpected module item: " << module_item.id();
  }
}

/*******************************************************************\

Function: verilog_typecheckt::convert_statements

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::convert_statements(
  verilog_module_exprt &verilog_module_expr)
{
  // Do defparam, also known as 'parameter override'.
  // These must all be done before any module instantiation,
  // which use the parameters.
  for(auto &item : verilog_module_expr.module_items())
  {
    if(item.id() == ID_parameter_override)
      convert_parameter_override(to_verilog_parameter_override(item));
    else if(item.id() == ID_set_genvars)
    {
      for(auto &sub_item : item.operands())
      {
        if(sub_item.id() == ID_parameter_override)
          convert_parameter_override(to_verilog_parameter_override(sub_item));
      }
    }
  }

  // typecheck the new module items
  for(auto &item : verilog_module_expr.module_items())
    convert_module_item(item);
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
  symbol.pretty_name=strip_verilog_prefix(full_identifier);

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
  module_identifier = module_symbol.name;

  const auto &module_source =
    to_verilog_module_source(module_symbol.type.find(ID_module_source));

  // Elaborate the named constants (parameters, enums),
  // generate constructs, and add the symbols to the symbol table.
  auto verilog_module_expr = elaborate(module_source);

  // Create symbols for the functions, tasks, registers/variables and wires.
  for(auto &module_item : verilog_module_expr.module_items())
    interface_module_item(module_item);

  // Check the module interface
  check_module_ports(module_source.ports());

  // Now typecheck the generated statements.
  convert_statements(verilog_module_expr);

  // store the module expression in module_symbol.value
  module_symbol.value = std::move(verilog_module_expr);
}

/*******************************************************************\

Function: verilog_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_typecheck(
  const verilog_parse_treet &parse_tree,
  symbol_table_baset &symbol_table,
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
  symbol_table_baset &symbol_table,
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
    return true;
  }

  verilog_typecheckt verilog_typecheck(*new_symbol, symbol_table, message_handler);
  return verilog_typecheck.typecheck_main();
}
