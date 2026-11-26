/*******************************************************************\

Module: VHDL Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "vhdl_typecheck.h"
#include "vhdl_typecheck_class.h"

#include <util/arith_tools.h>
#include <util/symbol_table_base.h>

#include <verilog/verilog_types.h>

#include <algorithm>

irep_idt vhdl_typecheckt::to_lower(irep_idt src)
{
  std::string data = id2string(src);
  std::transform(data.begin(), data.end(), data.begin(), ::tolower);
  return data;
}

std::optional<vhdl_typecheckt::declarationt>
vhdl_typecheckt::lookup(irep_idt name) const
{
  // IEEE 1076-2008 12.3: an inner declaration hides an outer homograph,
  // except that enumeration literals are overloadable: the literals of
  // all enclosing regions are visible, up to a declaration of the name
  // that is not a literal
  std::optional<declarationt> literals;

  for(auto s_it = scopes.rbegin(); s_it != scopes.rend(); s_it++)
  {
    auto d_it = s_it->declarations.find(name);
    if(d_it == s_it->declarations.end())
      continue;

    if(d_it->second.kind != declarationt::LITERALS)
      return literals.has_value() ? literals : std::optional{d_it->second};

    if(!literals.has_value())
      literals = d_it->second;
    else
      for(auto &literal : d_it->second.literals)
        literals->literals.push_back(literal);
  }

  return literals;
}

void vhdl_typecheckt::declare(
  irep_idt base_name,
  declarationt declaration,
  const source_locationt &source_location)
{
  auto lower_case_name = to_lower(base_name);
  auto &declarations = current_scope().declarations;
  auto d_it = declarations.find(lower_case_name);

  if(d_it == declarations.end())
  {
    declarations.emplace(lower_case_name, std::move(declaration));
    return;
  }

  // IEEE 1076-2008 5.2.2.1: enumeration literals may be overloaded
  if(
    d_it->second.kind == declarationt::LITERALS &&
    declaration.kind == declarationt::LITERALS)
  {
    for(auto &literal : declaration.literals)
      d_it->second.literals.push_back(std::move(literal));
    return;
  }

  throw errort{}.with_location(source_location)
    << "`" << base_name << "' is already declared";
}

std::optional<typet> vhdl_typecheckt::lookup_type(irep_idt name) const
{
  auto declaration = lookup(name);
  if(declaration.has_value() && declaration->kind == declarationt::TYPE)
    return declaration->type;
  else
    return {};
}

std::optional<exprt> vhdl_typecheckt::lookup_constant(irep_idt name) const
{
  auto declaration = lookup(name);
  if(declaration.has_value() && declaration->kind == declarationt::CONSTANT)
    return declaration->value;
  else
    return {};
}

const symbolt *vhdl_typecheckt::lookup_object(irep_idt name) const
{
  auto declaration = lookup(name);
  if(declaration.has_value() && declaration->kind == declarationt::OBJECT)
    return &symbol_table.lookup_ref(declaration->symbol);
  else
    return nullptr;
}

symbolt &vhdl_typecheckt::add_object(
  irep_idt base_name,
  const typet &type,
  const source_locationt &source_location)
{
  auto lower_case_name = to_lower(base_name);

  symbolt new_symbol;
  new_symbol.base_name = base_name;
  new_symbol.name =
    id2string(current_scope().prefix) + "." + id2string(lower_case_name);
  new_symbol.pretty_name = new_symbol.name;
  new_symbol.type = type;
  new_symbol.mode = ID_VHDL;
  new_symbol.module = module_symbol->name;
  new_symbol.location = source_location;

  declarationt declaration;
  declaration.kind = declarationt::OBJECT;
  declaration.symbol = new_symbol.name;
  declare(base_name, std::move(declaration), source_location);

  symbolt *symbol_ptr;
  if(symbol_table.move(new_symbol, symbol_ptr))
    throw errort{}.with_location(source_location)
      << "symbol `" << new_symbol.name << "' is already in the symbol table";

  return *symbol_ptr;
}

/// The predefined types of package STANDARD (IEEE 1076-2008 16.3), and
/// the types of the IEEE packages std_logic_1164 and numeric_std.
/// Use clauses are not checked.
void vhdl_typecheckt::add_predefined_types()
{
  auto add_type = [this](irep_idt name, typet type)
  {
    declarationt declaration;
    declaration.kind = declarationt::TYPE;
    declaration.type = std::move(type);
    declare(name, std::move(declaration), source_locationt::nil());
  };

  add_type("boolean", vhdl_boolean_type());
  add_type("bit", vhdl_bit_type());
  add_type("integer", vhdl_integer_type());
  add_type("natural", vhdl_natural_type());
  add_type("positive", vhdl_positive_type());
  add_type("std_logic", vhdl_std_logic_type());
  add_type("std_ulogic", vhdl_std_ulogic_type());

  // the unconstrained array types; the range is set when constrained
  for(auto name :
      {"bit_vector",
       "std_logic_vector",
       "std_ulogic_vector",
       "unsigned",
       "signed"})
    add_type(name, vhdl_unconstrained_array_type(name));

  // the literals of boolean; those of bit and std_ulogic are
  // character literals, which are not names
  for(auto literal : {"false", "true"})
  {
    declarationt declaration;
    declaration.kind = declarationt::LITERALS;
    declaration.literals.push_back(
      constant_exprt{literal, vhdl_boolean_type()});
    declare(literal, std::move(declaration), source_locationt::nil());
  }
}

/// IEEE 1076-2008 12.4: the use clauses in the design file, which
/// determine which operators of the IEEE packages are available
void vhdl_typecheckt::collect_use_clauses()
{
  for(auto &item : parse_tree.items)
    if(item.is_use())
      for(auto &name : item.use_names())
      {
        // library.package.all or library.package.item
        exprt package = static_cast<const exprt &>(name);
        if(package.id() == ID_all || package.id() == ID_member)
          package = to_unary_expr(package).op();
        if(package.id() == ID_member)
          packages_used.insert(
            to_lower(to_member_expr(package).get_component_name()));
        else if(package.id() == ID_symbol)
          packages_used.insert(
            to_lower(to_symbol_expr(package).get_identifier()));
      }
}

void vhdl_typecheckt::typecheck_interface_list(
  const irept::subt &list,
  bool is_generic)
{
  for(auto &element_irep : list)
  {
    auto &element = to_vhdl_object_declaration(element_irep);
    auto type = typecheck_subtype_indication(element.subtype_indication());
    auto &init = element.initial_value();
    auto mode = element.mode();

    exprt init_value = nil_exprt{};
    if(init.is_not_nil())
    {
      init_value = convert_to(typecheck_expr(init), type);
      // IEEE 1076-2008 6.5.6.3: the constraint of a generic of an
      // unconstrained type comes from its default value
      if(is_unconstrained_array(type))
        type = init_value.type();
    }

    // The constraint of a port of an unconstrained type comes from the
    // port map of the instantiation (IEEE 1076-2008 6.5.6.3); there is
    // none for the top-level entity.
    if(is_unconstrained_array(type))
    {
      // the interface element has no location of its own
      auto &first_declarator =
        static_cast<const exprt &>(element.declarators().front());
      throw errort{}.with_location(first_declarator.source_location())
        << "type `" << vhdl_type_to_string(type) << "' requires a constraint";
    }

    if(init.is_nil() && !is_generic && mode != ID_input)
    {
      // IEEE 1076-2008 6.4.2.3: T'left, as for signals
      init_value = default_value(type);
    }

    for(auto &declarator_irep : element.declarators())
    {
      auto &declarator =
        to_symbol_expr(static_cast<const exprt &>(declarator_irep));
      auto base_name = declarator.get_identifier();
      auto &source_location = declarator.source_location();

      if(is_generic)
      {
        // Generics are constants. We only support the default value.
        if(init_value.is_nil())
          throw errort{}.with_location(source_location)
            << "generic `" << base_name << "' has no default value";

        declarationt declaration;
        declaration.kind = declarationt::CONSTANT;
        declaration.value = init_value;
        declare(base_name, std::move(declaration), source_location);
      }
      else
      {
        auto &symbol = add_object(base_name, type, source_location);
        // inout ports may be driven by the environment, and are
        // treated like inputs unless assigned
        symbol.is_input = mode == ID_input || mode == ID_inout;
        symbol.is_output =
          mode == ID_output || mode == ID_vhdl_buffer || mode == ID_inout;
        symbol.is_state_var = !symbol.is_input;
        symbol.value = init_value;

        // add to the ports of the module
        irep_idt direction = mode == ID_input   ? ID_input
                             : mode == ID_inout ? ID_inout
                                                : ID_output;
        module_typet::portt port{
          symbol.name, symbol.base_name, symbol.type, direction};
        port.add(ID_C_source_location) = source_location;
        to_module_type(module_symbol->type).ports().push_back(std::move(port));
      }
    }
  }
}

void vhdl_typecheckt::typecheck_entity(const vhdl_parse_treet::itemt &entity)
{
  typecheck_interface_list(entity.generics(), true);
  typecheck_interface_list(entity.ports(), false);
  typecheck_declarations(entity.declarations());
}

void vhdl_typecheckt::typecheck_declarations(const irept &decl)
{
  for(auto &d : decl.get_sub())
    typecheck_declaration(d);
}

void vhdl_typecheckt::typecheck_declaration(const irept &decl_irep)
{
  auto &decl = static_cast<const exprt &>(decl_irep);
  auto &source_location = decl.source_location();

  if(
    decl.id() == ID_signal || decl.id() == ID_vhdl_variable ||
    decl.id() == ID_constant)
  {
    typecheck_object_declaration(to_vhdl_object_declaration(decl));
  }
  else if(decl.id() == ID_vhdl_type_decl)
  {
    typecheck_type_declaration(to_vhdl_type_declaration(decl));
  }
  else if(decl.id() == ID_vhdl_subtype_decl)
  {
    typecheck_subtype_declaration(to_vhdl_type_declaration(decl));
  }
  else if(decl.id() == ID_component)
  {
    throw errort{}.with_location(source_location)
      << "component declarations are not supported yet";
  }
  else if(decl.id() == ID_vhdl_function || decl.id() == ID_vhdl_procedure)
  {
    throw errort{}.with_location(source_location)
      << "subprogram declarations are not supported yet";
  }
  else if(decl.id() == ID_alias)
  {
    throw errort{}.with_location(source_location)
      << "alias declarations are not supported yet";
  }
  else
    throw errort{}.with_location(source_location)
      << "unexpected declaration: " << decl.id();
}

void vhdl_typecheckt::typecheck_object_declaration(
  const vhdl_object_declarationt &decl)
{
  auto type = typecheck_subtype_indication(decl.subtype_indication());
  auto &init = decl.initial_value();
  auto &source_location = decl.source_location();

  exprt init_value;

  if(init.is_not_nil())
  {
    init_value = convert_to(typecheck_expr(init), type);

    // IEEE 1076-2008 6.4.2.2: the constraint of a constant of an
    // unconstrained type comes from its value
    if(is_unconstrained_array(type))
      type = init_value.type();
  }
  else if(decl.id() == ID_constant)
    throw errort{}.with_location(source_location)
      << "constant declaration requires a value";

  // IEEE 1076-2008 6.4.2.3: signals and variables require a constrained
  // subtype
  if(is_unconstrained_array(type))
    throw errort{}.with_location(source_location)
      << "type `" << vhdl_type_to_string(type) << "' requires a constraint";

  if(init.is_nil())
    init_value = default_value(type);

  for(auto &declarator_irep : decl.declarators())
  {
    auto &declarator =
      to_symbol_expr(static_cast<const exprt &>(declarator_irep));
    auto base_name = declarator.get_identifier();
    auto &source_location = declarator.source_location();

    if(decl.id() == ID_constant)
    {
      declarationt declaration;
      declaration.kind = declarationt::CONSTANT;
      declaration.value = init_value;
      declare(base_name, std::move(declaration), source_location);
    }
    else
    {
      auto &symbol = add_object(base_name, type, source_location);
      symbol.is_state_var = true;
      symbol.value = init_value;
      // Variables are marked as auxiliary; this distinguishes them
      // from signals, which matters for assignments within a process.
      symbol.is_auxiliary = decl.id() == ID_vhdl_variable;
    }
  }
}

void vhdl_typecheckt::typecheck_type_declaration(
  const vhdl_type_declarationt &decl)
{
  auto &name = decl.name();
  auto base_name = name.get_identifier();
  auto lower_case_name = to_lower(base_name);

  auto type = typecheck_type(decl.definition());

  // a type definition yields a new type, named after the declaration;
  // a subtype indication yields a subtype
  if(decl.definition().id() == ID_vhdl_subtype_indication)
    static_cast<vhdl_typet &>(type).set_name(lower_case_name);
  else
  {
    type.set(ID_identifier, lower_case_name);
    type.set(ID_vhdl_base_type, lower_case_name);
  }

  if(type.id() == ID_vhdl_enumeration)
  {
    // the literals that are identifiers become constants of the type;
    // they may be overloaded (IEEE 1076-2008 5.2.2.1). Character
    // literals are not names, and are found through the type.
    for(auto &element : to_vhdl_enumeration_type(type).elements())
    {
      irep_idt literal = element.id();
      if(vhdl_enumeration_typet::is_character_literal(literal))
        continue;
      declarationt declaration;
      declaration.kind = declarationt::LITERALS;
      declaration.literals.push_back(constant_exprt{literal, type});
      declare(literal, std::move(declaration), name.source_location());
    }
  }

  declarationt declaration;
  declaration.kind = declarationt::TYPE;
  declaration.type = std::move(type);
  declare(base_name, std::move(declaration), name.source_location());
}

void vhdl_typecheckt::typecheck_subtype_declaration(
  const vhdl_type_declarationt &decl)
{
  auto &name = decl.name();
  auto base_name = name.get_identifier();

  auto type = typecheck_subtype_indication(decl.definition());
  static_cast<vhdl_typet &>(type).set_name(to_lower(base_name));

  declarationt declaration;
  declaration.kind = declarationt::TYPE;
  declaration.type = std::move(type);
  declare(base_name, std::move(declaration), name.source_location());
}

exprt vhdl_typecheckt::typecheck_concurrent_statements(const irept &body)
{
  exprt result(ID_body);

  for(auto &statement : body.get_sub())
    result.add_to_operands(
      typecheck_concurrent_statement(static_cast<const exprt &>(statement)));

  return result;
}

void vhdl_typecheckt::declare_label(
  irep_idt label,
  const source_locationt &source_location)
{
  if(label.empty())
    return;

  declarationt declaration;
  declaration.kind = declarationt::LABEL;
  declare(label, std::move(declaration), source_location);
}

exprt vhdl_typecheckt::typecheck_concurrent_statement(exprt statement)
{
  // IEEE 1076-2008 12.1: the label of a concurrent statement is
  // declared in the enclosing declarative region
  declare_label(
    to_vhdl_statement(statement).label(), statement.source_location());

  if(statement.id() == ID_process)
  {
    return typecheck_process(std::move(statement));
  }
  else if(statement.id() == ID_assert)
  {
    return typecheck_assert(std::move(statement));
  }
  else if(statement.id() == ID_vhdl_signal_assign)
  {
    return typecheck_assign(std::move(statement), true);
  }
  else if(statement.id() == ID_vhdl_selected_assign)
  {
    return typecheck_selected_assign(std::move(statement), true);
  }
  else if(statement.id() == ID_inst)
  {
    throw errort{}.with_location(statement.source_location())
      << "component instantiation is not supported yet";
  }
  else if(statement.id() == ID_generate_if || statement.id() == ID_generate_for)
  {
    throw errort{}.with_location(statement.source_location())
      << "generate statements are not supported yet";
  }
  else
    throw errort{}.with_location(statement.source_location())
      << "unexpected concurrent statement: " << statement.id();
}

exprt vhdl_typecheckt::typecheck_process(exprt expr)
{
  auto &process = to_vhdl_process(expr);

  // the declarations are scoped to the process
  auto label = process.label();
  irep_idt prefix =
    id2string(current_scope().prefix) + "." +
    (label.empty() ? "process#" + std::to_string(++process_counter)
                   : id2string(to_lower(label)));

  push_scope(prefix);

  typecheck_declarations(process.declarations());

  // the sensitivity list; we check that the names resolve
  auto &sensitivity = process.sensitivity();

  if(sensitivity.id() != ID_all && sensitivity.is_not_nil())
  {
    exprt new_sensitivity{ID_vhdl_sensitivity};
    for(auto &name : sensitivity.get_sub())
    {
      auto typed = typecheck_expr(static_cast<const exprt &>(name));
      new_sensitivity.move_to_sub(typed);
    }
    sensitivity = std::move(new_sensitivity);
  }

  // the body
  process.body() = typecheck_code(std::move(process.body()));

  pop_scope();

  return std::move(process);
}

codet vhdl_typecheckt::typecheck_code(exprt statement)
{
  if(statement.id() == ID_block)
    return typecheck_block(std::move(statement));
  else if(statement.id() == ID_assert)
    return typecheck_assert(std::move(statement));
  else if(statement.id() == ID_assign)
    return typecheck_assign(std::move(statement), false);
  else if(statement.id() == ID_vhdl_signal_assign)
    return typecheck_assign(std::move(statement), true);
  else if(statement.id() == ID_vhdl_selected_assign)
    return typecheck_selected_assign(
      std::move(statement),
      !to_vhdl_selected_assign(statement).is_variable_assignment());
  else if(statement.id() == ID_ifthenelse)
    return typecheck_if(std::move(statement));
  else if(statement.id() == ID_switch_case)
    return typecheck_case(std::move(statement));
  else if(statement.id() == ID_for)
    return typecheck_for(std::move(statement));
  else if(statement.id() == ID_skip)
    return code_skipt{};
  else if(statement.id() == ID_vhdl_report)
    return code_skipt{}; // no effect on the hardware
  else if(statement.id() == ID_wait)
    throw errort{}.with_location(statement.source_location())
      << "wait statements are not supported";
  else if(
    statement.id() == ID_while || statement.id() == ID_vhdl_exit ||
    statement.id() == ID_vhdl_next)
    throw errort{}.with_location(statement.source_location())
      << statement.id() << " statements are not supported yet";
  else if(statement.id() == ID_function_call)
    throw errort{}.with_location(statement.source_location())
      << "procedure calls are not supported yet";
  else if(statement.id() == ID_return)
    throw errort{}.with_location(statement.source_location())
      << "return statement outside of a subprogram";
  else
    throw errort{}.with_location(statement.source_location())
      << "unexpected statement: " << statement.id();
}

codet vhdl_typecheckt::typecheck_block(exprt block)
{
  code_blockt result;
  result.add_source_location() = block.source_location();

  for(auto &statement : block.operands())
    result.add(typecheck_code(std::move(statement)));

  return std::move(result);
}

/// IEEE 1076-2008 9.2.9: a condition is a boolean expression, or, with
/// the implicit condition operator ??, an expression of type bit or
/// std_ulogic, where '1' is true
exprt vhdl_typecheckt::typecheck_condition(exprt expr)
{
  auto result = typecheck_expr(std::move(expr));

  if(is_vhdl_scalar_bit_type(result.type()))
    return typecast_exprt{std::move(result), vhdl_boolean_type()};
  else
    return convert_to(std::move(result), vhdl_boolean_type());
}

codet vhdl_typecheckt::typecheck_assert(exprt expr)
{
  auto &assertion = to_vhdl_assert(expr);
  auto condition = typecheck_condition(assertion.condition());

  // The report is an expression of type string; we only support
  // string literals.
  auto &report = assertion.report();

  if(
    report.is_not_nil() &&
    (report.id() != ID_constant || report.type().id() != ID_string))
    throw errort{}.with_location(report.source_location())
      << "only string literals are supported in report clauses";

  // the severity level is ignored

  vhdl_code_assertt result{std::move(condition), assertion.label(), report};
  result.add_source_location() = assertion.source_location();
  return std::move(result);
}

codet vhdl_typecheckt::typecheck_assign(exprt assignment, bool is_signal)
{
  auto &binary = to_binary_expr(assignment);
  auto target = typecheck_expr(binary.lhs());

  // the target must be an object of the right class
  // the object is operand 0 of these
  exprt base = target;
  while(base.id() == ID_index || base.id() == ID_vhdl_slice ||
        base.id() == ID_member)
    base = base.operands().front();

  if(base.id() != ID_symbol)
    throw errort{}.with_location(target.source_location())
      << "assignment target must be a signal or a variable";

  auto &symbol = ns.lookup(to_symbol_expr(base));
  bool target_is_signal = !symbol.is_auxiliary;

  if(symbol.is_input && !symbol.is_output)
    throw errort{}.with_location(target.source_location())
      << "cannot assign to input port `" << symbol.base_name << "'";

  if(is_signal && !target_is_signal)
    throw errort{}.with_location(target.source_location())
      << "signal assignment to variable `" << symbol.base_name << "'";

  if(!is_signal && target_is_signal)
    throw errort{}.with_location(target.source_location())
      << "variable assignment to signal `" << symbol.base_name << "'";

  // The value is an expression, or a conditional, i.e., nested if
  // expressions with a nil else branch when there is none, for the
  // VHDL-2008 conditional assignment.
  auto convert_value = [this, &target](exprt value) -> exprt
  {
    std::function<exprt(exprt)> rec = [&](exprt v) -> exprt
    {
      if(v.id() == ID_if)
      {
        auto &if_expr = to_if_expr(v);
        if_expr.cond() = typecheck_condition(if_expr.cond());
        if_expr.true_case() = rec(if_expr.true_case());
        if(if_expr.false_case().is_not_nil())
          if_expr.false_case() = rec(if_expr.false_case());
        if_expr.type() = target.type();
        return std::move(if_expr);
      }
      else if(v.is_nil())
        return v; // unaffected
      else
        return convert_to(typecheck_expr(v), target.type());
    };
    return rec(std::move(value));
  };

  auto value = convert_value(binary.rhs());

  vhdl_code_assignt result{is_signal, std::move(target), std::move(value)};
  result.add_source_location() = assignment.source_location();
  return std::move(result);
}

/// IEEE 1076-2008 5.2.2.1: the position number of a static value of a
/// discrete type; for an array of an enumeration type, the number given
/// by the positions of the elements. This is used to compare choices.
std::optional<mp_integer>
vhdl_typecheckt::position_number(const exprt &expr) const
{
  auto &type = expr.type();

  if(type.id() == ID_vhdl_enumeration)
  {
    if(!expr.is_constant())
      return {};
    auto position = to_vhdl_enumeration_type(type).position(
      to_constant_expr(expr).get_value());
    if(!position.has_value())
      return {};
    return mp_integer(*position);
  }
  else if(type.id() == ID_vhdl_integer)
  {
    return constant_value(expr);
  }
  else if(type.id() == ID_vhdl_array && expr.id() == ID_array)
  {
    auto element_values =
      number_of_values(to_vhdl_array_type(type).element_type());
    if(!element_values.has_value())
      return {};

    // the elements are given from the left
    mp_integer result = 0;
    for(auto &element : expr.operands())
    {
      auto position = position_number(element);
      if(!position.has_value())
        return {};
      result = result * *element_values + *position;
    }
    return result;
  }
  else
    return {};
}

/// The number of values of a type, if known. std_ulogic has nine
/// values, of which we model two; a case statement on std_ulogic
/// requires an others choice, as in VHDL.
std::optional<mp_integer> vhdl_typecheckt::number_of_values(const typet &type)
{
  if(type.id() == ID_vhdl_enumeration)
    return to_vhdl_enumeration_type(type).elements().size();
  else if(type.id() == ID_vhdl_integer)
    return to_vhdl_integer_type(type).range().length();
  else if(
    type.id() == ID_vhdl_array && to_vhdl_array_type(type).is_constrained())
  {
    auto &array_type = to_vhdl_array_type(type);
    auto element_values = number_of_values(array_type.element_type());
    if(!element_values.has_value())
      return {};
    return power(*element_values, array_type.length());
  }
  else
    return {};
}

/// a value of the given type, for messages
std::string
vhdl_typecheckt::value_to_string(const mp_integer &value, const typet &type)
{
  if(type.id() == ID_vhdl_enumeration)
  {
    auto &enumeration_type = to_vhdl_enumeration_type(type);
    return id2string(
      enumeration_type.literal(numeric_cast_v<std::size_t>(value)));
  }
  else if(type.id() == ID_vhdl_array)
  {
    auto &array_type = to_vhdl_array_type(type);
    auto element_values = number_of_values(array_type.element_type());
    auto &element_type = to_vhdl_enumeration_type(array_type.element_type());
    auto length = numeric_cast_v<std::size_t>(array_type.length());

    std::string result(length, ' ');
    mp_integer remaining = value;
    for(std::size_t i = length; i > 0; i--)
    {
      auto digit = remaining % *element_values;
      remaining /= *element_values;
      // the character of the literal, without its quotes
      result[i - 1] =
        id2string(element_type.literal(numeric_cast_v<std::size_t>(digit)))[1];
    }
    return '"' + result + '"';
  }
  else
    return integer2string(value);
}

/// The condition for the given choices of one alternative, as used in
/// case statements and selected signal assignments. The values
/// covered are added to \p choices.
exprt vhdl_typecheckt::case_condition(
  const exprt &selector,
  const irept::subt &choice_list,
  choicest &choices)
{
  exprt::operandst disjuncts;

  for(auto &choice_irep : choice_list)
  {
    auto &choice = static_cast<const exprt &>(choice_irep);

    if(choice.id() == ID_vhdl_others)
    {
      // IEEE 1076-2008 10.9: the only choice of the last alternative
      if(choice_list.size() != 1)
        throw errort{}.with_location(choice.source_location())
          << "others must be the only choice of the alternative";

      choices.others = true;
      return true_exprt{};
    }
    else if(choice.id() == ID_range)
    {
      auto range = typecheck_range(choice);
      auto low = convert_to(
        vhdl_integer_constant(range.low(), vhdl_integer_type()),
        selector.type());
      auto high = convert_to(
        vhdl_integer_constant(range.high(), vhdl_integer_type()),
        selector.type());

      // a null range covers nothing
      if(range.length() != 0)
        choices.intervals.push_back(
          {range.low(), range.high(), choice.source_location()});

      disjuncts.push_back(and_exprt{
        binary_relation_exprt{low, ID_le, selector},
        binary_relation_exprt{selector, ID_le, high}});
    }
    else
    {
      // IEEE 1076-2008 10.9: the choices are locally static
      auto value = convert_to(typecheck_expr(choice), selector.type());
      auto position = position_number(value);

      if(!position.has_value())
        throw errort{}.with_location(choice.source_location())
          << "case choice must be a static expression";

      choices.intervals.push_back(
        {*position, *position, choice.source_location()});

      disjuncts.push_back(equal_exprt{selector, value});
    }
  }

  return disjunction(disjuncts);
}

/// IEEE 1076-2008 10.9: each value of the type of the selector is
/// covered by exactly one choice, or there is an others choice
void vhdl_typecheckt::check_choices(
  choicest &choices,
  const typet &type,
  const source_locationt &source_location)
{
  auto &intervals = choices.intervals;

  std::sort(
    intervals.begin(),
    intervals.end(),
    [](const choicest::intervalt &a, const choicest::intervalt &b)
    { return a.low < b.low; });

  mp_integer covered = 0;

  for(std::size_t i = 0; i < intervals.size(); i++)
  {
    if(i > 0 && intervals[i].low <= intervals[i - 1].high)
      throw errort{}.with_location(intervals[i].source_location)
        << "the choice " << value_to_string(intervals[i].low, type)
        << " is given more than once";

    covered += intervals[i].high - intervals[i].low + 1;
  }

  if(choices.others)
    return;

  auto values = number_of_values(type);

  if(!values.has_value() || covered != *values)
    throw errort{}.with_location(source_location)
      << "the choices do not cover all values of " << vhdl_type_to_string(type)
      << "; add an others choice";
}

/// The conditions for the alternatives of a case statement or selected
/// assignment (IEEE 1076-2008 10.9). The choices must be static, and
/// cover each value of the subtype of the selector exactly once;
/// others, if present, is the last alternative. As the choices are
/// complete, the last alternative is the remaining case, and gets the
/// condition true.
std::vector<exprt> vhdl_typecheckt::case_conditions(
  const exprt &selector,
  const irept::subt &alternatives,
  const source_locationt &source_location)
{
  if(is_vhdl_universal_type(selector.type()))
    throw errort{}.with_location(selector.source_location())
      << "cannot determine the type of the selector";

  choicest choices;
  std::vector<exprt> conditions;
  conditions.reserve(alternatives.size());

  for(std::size_t i = 0; i < alternatives.size(); i++)
  {
    auto &alternative = to_vhdl_case_alternative(alternatives[i]);
    bool others_seen = choices.others;

    conditions.push_back(
      case_condition(selector, alternative.choices(), choices));

    if(choices.others && !others_seen && i + 1 != alternatives.size())
      throw errort{}.with_location(alternative.source_location())
        << "others must be the last alternative";
  }

  check_choices(choices, selector.type(), source_location);

  if(!conditions.empty())
    conditions.back() = true_exprt{};

  return conditions;
}

codet vhdl_typecheckt::typecheck_selected_assign(
  exprt assignment,
  bool is_signal)
{
  // We turn this into nested if statements.
  auto &selected_assignment = to_vhdl_selected_assign(assignment);
  auto selector = typecheck_expr(selected_assignment.selector());
  auto &alternatives = selected_assignment.alternatives();
  auto conditions =
    case_conditions(selector, alternatives, assignment.source_location());

  // we go backwards, starting from the last alternative
  codet result = code_skipt{};

  for(std::size_t i = alternatives.size(); i > 0; i--)
  {
    auto &alternative = to_vhdl_case_alternative(alternatives[i - 1]);

    // the assignment of the value of this alternative
    exprt plain_assignment(is_signal ? ID_vhdl_signal_assign : ID_assign);
    plain_assignment.add_source_location() = alternative.source_location();
    plain_assignment.add_to_operands(
      exprt{selected_assignment.target()}, exprt{alternative.body()});
    auto assignment_code = typecheck_assign(plain_assignment, is_signal);

    if(conditions[i - 1].is_true()) // the last alternative
      result = std::move(assignment_code);
    else
      result = code_ifthenelset{
        std::move(conditions[i - 1]),
        std::move(assignment_code),
        std::move(result)};
  }

  result.add_source_location() = assignment.source_location();
  return result;
}

codet vhdl_typecheckt::typecheck_if(exprt if_statement)
{
  auto &operands = if_statement.operands();
  DATA_INVARIANT(operands.size() == 3, "if statements have three operands");

  auto condition = typecheck_condition(operands[0]);
  auto then_case = typecheck_code(operands[1]);

  code_ifthenelset result{std::move(condition), std::move(then_case)};
  result.add_source_location() = if_statement.source_location();

  if(operands[2].is_not_nil())
    result.else_case() = typecheck_code(operands[2]);

  return std::move(result);
}

codet vhdl_typecheckt::typecheck_case(exprt expr)
{
  // We turn this into nested if statements.
  auto &case_statement = to_vhdl_case_statement(expr);
  auto selector = typecheck_expr(case_statement.selector());
  auto &alternatives = case_statement.alternatives();
  auto conditions =
    case_conditions(selector, alternatives, case_statement.source_location());

  // we go backwards, starting from the last alternative
  codet result = code_skipt{};

  for(std::size_t i = alternatives.size(); i > 0; i--)
  {
    auto &alternative = to_vhdl_case_alternative(alternatives[i - 1]);
    auto body = typecheck_code(alternative.body());

    if(conditions[i - 1].is_true()) // the last alternative
      result = std::move(body);
    else
    {
      code_ifthenelset if_code{
        std::move(conditions[i - 1]), std::move(body), std::move(result)};
      if_code.add_source_location() = alternative.source_location();
      result = std::move(if_code);
    }
  }

  result.add_source_location() = case_statement.source_location();
  return result;
}

codet vhdl_typecheckt::typecheck_for(exprt expr)
{
  auto &for_statement = to_vhdl_for_statement(expr);

  // The loop is unrolled; the loop variable is a constant in each copy.
  auto range = typecheck_range(for_statement.range());
  auto lower_case_name =
    to_lower(for_statement.loop_variable().get_identifier());

  if(range.length() > 10000)
    throw errort{}.with_location(for_statement.source_location())
      << "loop range too large";

  code_blockt result;
  result.add_source_location() = for_statement.source_location();

  // IEEE 1076-2008 10.10: a null range executes zero times
  if(range.length() == 0)
    return std::move(result);

  auto &body = for_statement.body();

  for(mp_integer i = range.left;;
      i += (range.direction == vhdl_directiont::TO ? 1 : -1))
  {
    push_scope(current_scope().prefix);
    declarationt loop_constant;
    loop_constant.kind = declarationt::CONSTANT;
    loop_constant.value = vhdl_integer_constant(i, vhdl_integer_type());
    declare(
      lower_case_name,
      std::move(loop_constant),
      for_statement.source_location());
    result.add(typecheck_code(body));
    pop_scope();

    if(i == range.right)
      break;
  }

  return std::move(result);
}

void vhdl_typecheckt::typecheck_architecture(
  const vhdl_parse_treet::itemt &item)
{
  // create the module symbol

  symbolt symbol;

  symbol.mode = ID_VHDL;
  symbol.name = "vhdl::" + id2string(module_name);
  symbol.type = module_typet{};
  symbol.base_name = module_name;
  symbol.pretty_name = module_name;
  symbol.module = symbol.name;
  symbol.location = item.source_location();

  symbolt *new_symbol;

  if(symbol_table.move(symbol, new_symbol))
    throw errort{}.with_location(item.source_location())
      << "duplicate definition of module " << symbol.base_name;

  module_symbol = new_symbol;

  collect_use_clauses();

  // The predefined declarations, the packages in the design file, and
  // the entity with its architecture are in nested declarative regions,
  // so that an inner declaration hides an outer one.
  push_scope(module_symbol->name);
  add_predefined_types();

  push_scope(module_symbol->name);
  for(auto &p : parse_tree.items)
    if(p.is_package())
      typecheck_package(p);

  push_scope(module_symbol->name);

  // find the entity
  const vhdl_parse_treet::itemt *entity = nullptr;
  for(auto &e : parse_tree.items)
    if(e.is_entity() && e.get_identifier() == module_name)
      entity = &e;

  if(entity == nullptr)
    throw errort{}.with_location(item.source_location())
      << "entity `" << module_name << "' not found";

  typecheck_entity(*entity);

  // now the architecture
  typecheck_declarations(item.declarations());

  auto body = typecheck_concurrent_statements(item.body());

  pop_scope();
  pop_scope();
  pop_scope();

  new_symbol->value.id(ID_module);
  new_symbol->value.add(ID_body) = std::move(body);
}

/// We only support constants, types and subtypes in packages.
void vhdl_typecheckt::typecheck_package(const vhdl_parse_treet::itemt &package)
{
  for(auto &d : package.declarations().get_sub())
  {
    if(
      d.id() == ID_constant || d.id() == ID_vhdl_type_decl ||
      d.id() == ID_vhdl_subtype_decl)
    {
      typecheck_declaration(d);
    }
    else if(d.id() == ID_vhdl_function || d.id() == ID_vhdl_procedure)
    {
      // ignored, as they cannot be called yet
    }
    else
      throw errort{}.with_location(
        static_cast<const exprt &>(d).source_location())
        << "unsupported package declaration: " << d.id();
  }
}

void vhdl_typecheckt::typecheck()
{
  // The module is an entity. Find the architecture for the entity
  // in the parse tree; when there are multiple, the last one is used.
  const vhdl_parse_treet::itemt *architecture = nullptr;
  const vhdl_parse_treet::itemt *entity = nullptr;

  for(const auto &item : parse_tree.items)
  {
    if(item.is_architecture() && module_name == item.get_entity_identifier())
      architecture = &item;
    else if(item.is_entity() && module_name == item.get_identifier())
      entity = &item;
  }

  if(architecture == nullptr)
  {
    // the error is reported at the entity, if there is one
    auto location =
      entity != nullptr ? entity->source_location() : source_locationt::nil();
    throw errort{}.with_location(location)
      << "no architecture found for entity `" << module_name << "'";
  }

  typecheck_architecture(*architecture);
}

bool vhdl_typecheck(
  const vhdl_parse_treet &parse_tree,
  symbol_table_baset &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  return vhdl_typecheckt(parse_tree, module, symbol_table, message_handler)
    .typecheck_main();
}
