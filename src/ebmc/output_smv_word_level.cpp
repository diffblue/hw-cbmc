/*******************************************************************\

Module: Word-Level SMV Output

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "output_smv_word_level.h"

#include <util/bitvector_types.h>
#include <util/replace_symbol.h>

#include <smvlang/expr2smv.h>
#include <smvlang/smv_expr.h>
#include <temporal-logic/sva_to_ltl.h>
#include <trans-word-level/next_symbol.h>

#include "ebmc_error.h"
#include "ebmc_properties.h"
#include "transition_system.h"

#include <ostream>
#include <unordered_set>

std::string
smv_expr_printer(const exprt &expr, const replace_symbolt &smv_identifier_map)
{
  exprt tmp = expr; // copy

  // replace_symbolt does not do next_symbol; we hence replace next_symbol by
  // smv_next_exprt{symbol_exprt{...}} first.
  tmp.visit_pre(
    [](exprt &node)
    {
      if(node.id() == ID_next_symbol)
      {
        auto identifier = to_next_symbol_expr(node).identifier();
        node = smv_next_exprt{symbol_exprt{identifier, node.type()}};
      }
    });

  // now apply replace_symbolt
  smv_identifier_map(tmp);

  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  return expr2smv(tmp, ns);
}

class smv_type_printert
{
public:
  explicit smv_type_printert(const typet &__type) : _type(__type)
  {
  }

  const typet &type() const
  {
    return _type;
  }

protected:
  const typet &_type;
};

static bool is_supported_type(const typet &type)
{
  return type.id() == ID_bool || type.id() == ID_signedbv ||
         type.id() == ID_unsignedbv || type.id() == ID_range ||
         type.id() == ID_array;
}

std::ostream &
operator<<(std::ostream &out, const smv_type_printert &type_printer)
{
  auto &type = type_printer.type();

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  if(is_supported_type(type))
    return out << type2smv(type, ns);
  else
    throw ebmc_errort{} << "cannot convert type " << type.id() << " to SMV";

  return out;
}

/// Create an identifier that satisfies SMV's syntactic rules.
irep_idt create_smv_identifier(const irep_idt &identifier)
{
  PRECONDITION(!identifier.empty());

  std::string result;

  // must start with letter or _
  if(!isalpha(identifier[0]) && identifier[0] != '_')
    result = '_';

  // the rest must be alphanumeric, _ $ # -, or a complex identifier
  for(auto ch : id2string(identifier))
  {
    if(isalnum(ch) || ch == '_' || ch == '$' || ch == '#' || ch == '-')
      result += ch;
    else
      result += '_';
  }

  return result;
}

replace_symbolt smv_identifier_map(const transition_systemt &transition_system)
{
  const auto module = transition_system.main_symbol->name;
  const auto &symbol_table = transition_system.symbol_table;
  replace_symbolt result;
  std::unordered_set<irep_idt, irep_id_hash> identifiers_used;

  for(auto m_it = symbol_table.symbol_module_map.lower_bound(module);
      m_it != symbol_table.symbol_module_map.upper_bound(module);
      m_it++)
  {
    const irep_idt &identifier = m_it->second;

    symbol_tablet::symbolst::const_iterator s_it =
      symbol_table.symbols.find(identifier);

    if(s_it == symbol_table.symbols.end())
      throw ebmc_errort{} << "failed to find symbol " << identifier;

    const symbolt &symbol = s_it->second;

    if(is_supported_type(symbol.type))
    {
      // The SMV identifiers we generate might collide.
      std::size_t collision_counter = 1;
      irep_idt smv_identifier;

      do
      {
        smv_identifier = create_smv_identifier(
          !symbol.base_name.empty() ? symbol.base_name : symbol.name);

        if(collision_counter != 1)
          smv_identifier =
            id2string(smv_identifier) + '#' + std::to_string(collision_counter);

        collision_counter++;
      } while(!identifiers_used.insert(smv_identifier).second);

      smv_identifier_exprt replacement{smv_identifier, symbol.type};
      result.insert(symbol.symbol_expr(), replacement);
    }
  }

  return result;
}

static void smv_state_variables(
  const transition_systemt &transition_system,
  const replace_symbolt &identifier_map,
  std::ostream &out)
{
  bool found = false;

  const auto module = transition_system.main_symbol->name;
  const auto &symbol_table = transition_system.symbol_table;

  for(auto m_it = symbol_table.symbol_module_map.lower_bound(module);
      m_it != symbol_table.symbol_module_map.upper_bound(module);
      m_it++)
  {
    const irep_idt &identifier = m_it->second;

    symbol_tablet::symbolst::const_iterator s_it =
      symbol_table.symbols.find(identifier);

    if(s_it == symbol_table.symbols.end())
      throw ebmc_errort{} << "failed to find symbol " << identifier;

    const symbolt &symbol = s_it->second;

    if(is_supported_type(symbol.type) && !symbol.is_type && !symbol.is_property)
    {
      out << "VAR " << smv_expr_printer(symbol.symbol_expr(), identifier_map)
          << " : " << smv_type_printert{symbol.type} << ";\n";
      found = true;
    }
  }

  if(found)
    out << '\n';
}

static void smv_initial_states(
  const exprt &expr,
  const replace_symbolt &identifier_map,
  std::ostream &out)
{
  if(expr.id() == ID_and)
  {
    for(auto &conjunct : expr.operands())
      smv_initial_states(conjunct, identifier_map, out);
  }
  else if(expr.is_true())
  {
    // ignore
  }
  else
  {
    out << "INIT " << smv_expr_printer(expr, identifier_map) << '\n';
  }
}

static void smv_initial_states(
  const transition_systemt &transition_system,
  const replace_symbolt &identifier_map,
  std::ostream &out)
{
  smv_initial_states(transition_system.trans_expr.init(), identifier_map, out);
}

static void smv_invar_rec(
  const exprt &expr,
  const replace_symbolt &identifier_map,
  std::ostream &out)
{
  if(expr.id() == ID_and)
  {
    for(auto &conjunct : expr.operands())
      smv_invar_rec(conjunct, identifier_map, out);
  }
  else if(expr.is_true())
  {
    // ignore
  }
  else
  {
    out << "INVAR " << smv_expr_printer(expr, identifier_map) << '\n';
  }
}

static void smv_invar(
  const transition_systemt &transition_system,
  const replace_symbolt &identifier_map,
  std::ostream &out)
{
  smv_invar_rec(transition_system.trans_expr.invar(), identifier_map, out);
}

static void smv_transition_relation_rec(
  const exprt &expr,
  const replace_symbolt &identifier_map,
  std::ostream &out)
{
  if(expr.id() == ID_and)
  {
    for(auto &conjunct : expr.operands())
      smv_transition_relation_rec(conjunct, identifier_map, out);
  }
  else if(expr.is_true())
  {
    // ignore
  }
  else
  {
    out << "TRANS " << smv_expr_printer(expr, identifier_map) << '\n';
  }
}

static void smv_transition_relation(
  const transition_systemt &transition_system,
  const replace_symbolt &identifier_map,
  std::ostream &out)
{
  smv_transition_relation_rec(
    transition_system.trans_expr.trans(), identifier_map, out);
}

static void smv_properties(
  const transition_systemt &transition_system,
  const ebmc_propertiest &properties,
  const replace_symbolt &identifier_map,
  std::ostream &out)
{
  for(auto &property : properties.properties)
  {
    if(property.is_disabled() || property.is_assumed())
      continue;

    if(is_CTL(property.normalized_expr))
    {
      out << "CTLSPEC "
          << smv_expr_printer(property.normalized_expr, identifier_map);
    }
    else if(is_LTL(property.normalized_expr))
    {
      out << "LTLSPEC "
          << smv_expr_printer(property.normalized_expr, identifier_map);
    }
    else if(is_SVA(property.normalized_expr))
    {
      // we can turn some SVA properties into LTL
      try
      {
        auto ltl = SVA_to_LTL(property.normalized_expr);
        out << "LTLSPEC " << smv_expr_printer(ltl, identifier_map);
      }
      catch(sva_to_ltl_unsupportedt error)
      {
        out << "-- " << property.identifier << ": SVA " << error.expr.id()
            << " not converted\n";
      }
    }
    else
      out << "-- " << property.identifier << ": not converted\n";

    out << '\n';
  }
}

void output_smv_word_level(
  const transition_systemt &transition_system,
  const ebmc_propertiest &properties,
  std::ostream &out)
{
  out << "MODULE main\n\n";

  auto identifier_map = smv_identifier_map(transition_system);

  // state-holding elements first
  smv_state_variables(transition_system, identifier_map, out);

  // initial state constraints
  smv_initial_states(transition_system, identifier_map, out);

  // in-state invariants
  smv_invar(transition_system, identifier_map, out);

  // transition relation
  smv_transition_relation(transition_system, identifier_map, out);

  // properties
  smv_properties(transition_system, properties, identifier_map, out);
}
