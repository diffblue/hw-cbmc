/*******************************************************************\

Module: Liveness to Safety Translation

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Liveness to Safety Translation

#include "liveness_to_safety.h"

#include <util/invariant.h>
#include <util/namespace.h>

#include <trans-word-level/next_symbol.h>
#include <verilog/sva_expr.h>

#include "ebmc_error.h"

// Using terminology from
// https://fmv.jku.at/papers/BiereArthoSchuppan-FMICS02.pdf

class liveness_to_safetyt
{
public:
  liveness_to_safetyt(
    transition_systemt &_transition_system,
    ebmc_propertiest &_properties)
    : transition_system(_transition_system), properties(_properties)
  {
  }

  void operator()();

protected:
  transition_systemt &transition_system;
  ebmc_propertiest &properties;

  std::vector<symbol_exprt> state_vars;

  using propertyt = ebmc_propertiest::propertyt;

  void translate_GFp(propertyt &);

  static symbol_exprt loop_variable(const symbol_exprt &symbol_expr)
  {
    return symbol_exprt{
      id2string(symbol_expr.get_identifier()) + "#loop", symbol_expr.type()};
  }

  exprt state_is_loop() const
  {
    exprt::operandst conjuncts;

    for(auto &var : state_vars)
      conjuncts.push_back(equal_exprt(var, loop_variable(var)));

    return conjunction(std::move(conjuncts));
  }

  exprt next_loop_is_loop() const
  {
    exprt::operandst conjuncts;

    for(auto &var : state_vars)
      conjuncts.push_back(
        equal_exprt(next_symbol_exprt{loop_variable(var)}, loop_variable(var)));

    return conjunction(std::move(conjuncts));
  }

  exprt next_loop_is_state() const
  {
    exprt::operandst conjuncts;

    for(auto &var : state_vars)
      conjuncts.push_back(
        equal_exprt(next_symbol_exprt{loop_variable(var)}, var));

    return conjunction(std::move(conjuncts));
  }

  static symbol_exprt saved_symbol()
  {
    const static symbol_exprt expr("liveness-to-safety::saved", bool_typet());
    return expr;
  }

  static symbol_exprt save_symbol()
  {
    const static symbol_exprt expr("liveness-to-safety::save", bool_typet());
    return expr;
  }

  static symbol_exprt looped_symbol()
  {
    const static symbol_exprt expr("liveness-to-safety::looped", bool_typet());
    return expr;
  }

  static symbol_exprt live_symbol(irep_idt property_identifier)
  {
    return symbol_exprt(id2string(property_identifier) + "#live", bool_typet());
  }

  static exprt
  safety_replacement(irep_idt property_identifier, const exprt &expr)
  {
    // G (looped → live)
    return sva_always_exprt(
      implies_exprt(looped_symbol(), live_symbol(property_identifier)));
  }
};

/// returns true iff the given property is supported
/// by the liveness-to-safety translation
static bool property_supported(const exprt &expr)
{
  return expr.id() == ID_sva_always &&
         (to_sva_always_expr(expr).op().id() == ID_sva_eventually ||
          to_sva_always_expr(expr).op().id() == ID_sva_s_eventually);
}

static bool have_supported_property(const ebmc_propertiest &properties)
{
  for(auto &property : properties.properties)
    if(!property.is_disabled())
      if(property_supported(property.normalized_expr))
        return true;

  return false;
}

void liveness_to_safetyt::operator()()
{
  // Do we have a supported property?
  if(!have_supported_property(properties))
    return; // no

  // gather the state variables
  state_vars = transition_system.state_variables();

  const namespacet ns(transition_system.symbol_table);

  // create 'loop' shadow symbols for the state variables
  for(auto &symbol_expr : state_vars)
  {
    auto &var_symbol = ns.lookup(symbol_expr);

    auxiliary_symbolt loop_symbol{
      loop_variable(symbol_expr).get_identifier(),
      var_symbol.type,
      var_symbol.mode};

    loop_symbol.is_state_var = true;
    loop_symbol.module = var_symbol.module;
    loop_symbol.base_name = id2string(var_symbol.base_name) + "#loop";

    auto result = transition_system.symbol_table.insert(std::move(loop_symbol));
    CHECK_RETURN(result.second);
  }

  // create 'save' symbol (an input)
  {
    auxiliary_symbolt save_symbol{
      this->save_symbol().get_identifier(),
      this->save_symbol().type(),
      transition_system.main_symbol->mode};

    save_symbol.is_input = true;
    save_symbol.module = transition_system.main_symbol->module;
    save_symbol.base_name = "save";

    auto result = transition_system.symbol_table.insert(std::move(save_symbol));
    CHECK_RETURN(result.second);
  }

  // create 'saved' symbol (a state variable)
  {
    auxiliary_symbolt saved_symbol{
      this->saved_symbol().get_identifier(),
      this->saved_symbol().type(),
      transition_system.main_symbol->mode};

    saved_symbol.is_state_var = true;
    saved_symbol.module = transition_system.main_symbol->module;
    saved_symbol.base_name = "saved";

    auto result =
      transition_system.symbol_table.insert(std::move(saved_symbol));
    CHECK_RETURN(result.second);
  }

  // initial-state constraint for 'saved' variable
  auto saved_init = equal_exprt{saved_symbol(), false_exprt()};

  // next-state constraint for 'saved' variable
  // saved' := saved ∨ save
  auto saved_trans = equal_exprt{
    next_symbol_exprt{saved_symbol()}, or_exprt{saved_symbol(), save_symbol()}};

  // Rule out (save ∧ saved)
  auto save_invar =
    implies_exprt{symbol_exprt{save_symbol()}, not_exprt{saved_symbol()}};

  // next-state constraint for 'loop' variables
  // save ? loop'=state : loop'=loop
  // The paper uses
  // (save ∧ ¬saved) ? loop'=state : loop'=loop
  // but we have a constraint save → ¬saved to rule out the case (save ∧ saved).
  auto loop_trans = if_exprt{
    and_exprt{save_symbol(), not_exprt{saved_symbol()}},
    next_loop_is_state(),
    next_loop_is_loop()};

  // create the 'looped' symbol, a wire
  {
    auxiliary_symbolt looped_symbol{
      this->looped_symbol().get_identifier(),
      this->looped_symbol().type(),
      transition_system.main_symbol->mode};

    looped_symbol.is_state_var = false;
    looped_symbol.module = transition_system.main_symbol->module;

    auto result =
      transition_system.symbol_table.insert(std::move(looped_symbol));
    CHECK_RETURN(result.second);
  }

  // in-state constraint for 'looped' variable
  // looped := (saved ∧ state=loop)
  auto looped_invar = equal_exprt{
    this->looped_symbol(), and_exprt(saved_symbol(), state_is_loop())};

  transition_system.trans_expr.init() =
    conjunction({transition_system.trans_expr.init(), std::move(saved_init)});

  transition_system.trans_expr.invar() = conjunction(
    {transition_system.trans_expr.invar(),
     std::move(save_invar),
     std::move(looped_invar)});

  transition_system.trans_expr.trans() = conjunction(
    {transition_system.trans_expr.trans(),
     std::move(saved_trans),
     std::move(loop_trans)});

  for(auto &property : properties.properties)
  {
    if(!property.is_disabled())
    {
      // We want GFp.
      if(property_supported(property.normalized_expr))
      {
        translate_GFp(property);
      }
      else
      {
        throw ebmc_errort().with_location(property.location)
          << "no liveness-to-safety translation for " << property.description;
      }
    }
  }
}

void liveness_to_safetyt::translate_GFp(propertyt &property)
{
  auto &p = to_unary_expr(to_unary_expr(property.normalized_expr).op()).op();

  // create the 'live' symbol, one for each liveness property
  {
    auxiliary_symbolt live_symbol{
      this->live_symbol(property.name).get_identifier(),
      this->live_symbol(property.name).type(),
      transition_system.main_symbol->mode};

    live_symbol.is_state_var = true;
    live_symbol.module = transition_system.main_symbol->module;

    auto result = transition_system.symbol_table.insert(std::move(live_symbol));
    CHECK_RETURN(result.second);
  }

  // Initial-state constraint for 'live' variable.
  auto live_init = equal_exprt{live_symbol(property.name), false_exprt()};

  transition_system.trans_expr.init() =
    conjunction({transition_system.trans_expr.init(), std::move(live_init)});

  // Next-state constraint for 'live' variable.
  // The paper uses live' := live ∨ found, which is for F found,
  // but we use (live ∧ ¬save) ∨ found, to get GF found.
  auto live_trans = equal_exprt{
    next_symbol_exprt{live_symbol(property.name)},
    or_exprt{
      and_exprt{live_symbol(property.name), not_exprt{save_symbol()}}, p}};

  transition_system.trans_expr.trans() =
    conjunction({transition_system.trans_expr.trans(), std::move(live_trans)});

  // replace the liveness property
  property.normalized_expr =
    safety_replacement(property.name, property.normalized_expr);
}

void liveness_to_safety(
  transition_systemt &transition_system,
  ebmc_propertiest &properties)
{
  liveness_to_safetyt{transition_system, properties}();
}
