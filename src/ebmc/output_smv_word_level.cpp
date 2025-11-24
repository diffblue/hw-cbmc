/*******************************************************************\

Module: Word-Level SMV Output

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "output_smv_word_level.h"

#include <util/bitvector_types.h>

#include <smvlang/expr2smv.h>
#include <temporal-logic/sva_to_ltl.h>

#include "ebmc_error.h"
#include "ebmc_properties.h"
#include "transition_system.h"

#include <ostream>

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

std::ostream &
operator<<(std::ostream &out, const smv_type_printert &type_printer)
{
  auto &type = type_printer.type();

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  if(
    type.id() == ID_bool || type.id() == ID_signedbv ||
    type.id() == ID_unsignedbv || type.id() == ID_range ||
    type.id() == ID_array)
  {
    return out << type2smv(type, ns);
  }
  else
    throw ebmc_errort{} << "cannot convert type " << type.id() << " to SMV";

  return out;
}

static void smv_state_variables(
  const transition_systemt &transition_system,
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

    if(symbol.is_state_var)
    {
      if(symbol.is_input)
        out << "IVAR";
      else
        out << "VAR";

      out << ' ' << symbol.base_name << " : " << smv_type_printert{symbol.type}
          << ";\n";
      found = true;
    }
  }

  if(found)
    out << '\n';
}

static void
smv_initial_states(const exprt &expr, const namespacet &ns, std::ostream &out)
{
  if(expr.id() == ID_and)
  {
    for(auto &conjunct : expr.operands())
      smv_initial_states(conjunct, ns, out);
  }
  else if(expr.is_true())
  {
    // ignore
  }
  else
  {
    out << "INIT " << expr2smv(expr, ns) << '\n';
  }
}

static void smv_initial_states(
  const transition_systemt &transition_system,
  std::ostream &out)
{
  const namespacet ns(transition_system.symbol_table);
  smv_initial_states(transition_system.trans_expr.init(), ns, out);
}

static void
smv_invar(const exprt &expr, const namespacet &ns, std::ostream &out)
{
  if(expr.id() == ID_and)
  {
    for(auto &conjunct : expr.operands())
      smv_invar(conjunct, ns, out);
  }
  else if(expr.is_true())
  {
    // ignore
  }
  else
  {
    out << "INVAR " << expr2smv(expr, ns) << '\n';
  }
}

static void
smv_invar(const transition_systemt &transition_system, std::ostream &out)
{
  const namespacet ns(transition_system.symbol_table);
  smv_invar(transition_system.trans_expr.invar(), ns, out);
}

static void smv_transition_relation(
  const exprt &expr,
  const namespacet &ns,
  std::ostream &out)
{
  if(expr.id() == ID_and)
  {
    for(auto &conjunct : expr.operands())
      smv_transition_relation(conjunct, ns, out);
  }
  else if(expr.is_true())
  {
    // ignore
  }
  else
  {
    out << "TRANS " << expr2smv(expr, ns) << '\n';
  }
}

static void smv_transition_relation(
  const transition_systemt &transition_system,
  std::ostream &out)
{
  const namespacet ns(transition_system.symbol_table);
  smv_transition_relation(transition_system.trans_expr.trans(), ns, out);
}

static void smv_properties(
  const transition_systemt &transition_system,
  const ebmc_propertiest &properties,
  std::ostream &out)
{
  const namespacet ns(transition_system.symbol_table);

  for(auto &property : properties.properties)
  {
    if(property.is_disabled() || property.is_assumed())
      continue;

    if(is_CTL(property.normalized_expr))
    {
      out << "CTLSPEC " << expr2smv(property.normalized_expr, ns);
    }
    else if(is_LTL(property.normalized_expr))
    {
      out << "LTLSPEC " << expr2smv(property.normalized_expr, ns);
    }
    else if(is_SVA(property.normalized_expr))
    {
      // we can turn some SVA properties into LTL
      try
      {
        auto ltl = SVA_to_LTL(property.normalized_expr);
        out << "LTLSPEC " << expr2smv(ltl, ns);
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

  // state-holding elements first
  smv_state_variables(transition_system, out);

  // initial state constraints
  smv_initial_states(transition_system, out);

  // in-state invariants
  smv_invar(transition_system, out);

  // transition relation
  smv_transition_relation(transition_system, out);

  // properties
  smv_properties(transition_system, properties, out);
}
