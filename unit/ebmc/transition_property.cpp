/*******************************************************************\

Module: Transition Property Engine Unit Tests

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <ebmc/transition_property.h>
#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>
#include <temporal-logic/ltl.h>
#include <temporal-logic/normalize_property.h>
#include <testing-utils/use_catch.h>
#include <trans-word-level/next_symbol.h>
#include <verilog/sva_expr.h>

/// Build a transition system with a single Boolean state variable s
/// and transition relation next(s) = rhs.
static transition_systemt
make_transition_system(const irep_idt &name, const exprt &rhs)
{
  transition_systemt ts;

  // main module symbol
  symbolt module_symbol{"main", typet{ID_module}, ID_Verilog};
  module_symbol.base_name = "main";
  ts.symbol_table.add(module_symbol);
  ts.main_symbol = &ts.symbol_table.lookup_ref("main");

  // state variable
  symbolt var_symbol{name, rhs.type(), ID_Verilog};
  var_symbol.base_name = name;
  var_symbol.is_state_var = true;
  var_symbol.module = "main";
  ts.symbol_table.add(var_symbol);

  // Transition constraint: next(s) = rhs
  auto s_next = next_symbol_exprt{name, rhs.type()};
  auto trans = equal_exprt{s_next, rhs};

  ts.trans_expr = transt{ID_trans, true_exprt(), true_exprt(), trans, typet()};

  return ts;
}

static ebmc_solver_factoryt test_solver_factory()
{
  return [](const namespacet &ns, message_handlert &message_handler)
  {
    auto sat = std::make_unique<satcheckt>(message_handler);
    auto dec = std::make_unique<boolbvt>(ns, *sat, message_handler);
    return ebmc_solvert{std::move(sat), std::move(dec)};
  };
}

static ebmc_propertiest make_properties(const exprt &property_expr)
{
  ebmc_propertiest properties;
  ebmc_propertiest::propertyt p;
  p.identifier = "test.p";
  p.name = "test.p";
  p.original_expr = property_expr;
  p.normalized_expr = normalize_property(property_expr);
  p.mode = ID_Verilog;
  properties.properties.push_back(std::move(p));
  return properties;
}

SCENARIO("transition property: state predicate implied by transition relation")
{
  // s' = true, property: always s
  // The transition relation does not constrain s in the current state,
  // so this should be inconclusive.
  auto s = symbol_exprt{"s", bool_typet()};
  auto ts = make_transition_system("s", true_exprt());
  auto properties = make_properties(sva_always_exprt{s});
  null_message_handlert msg;

  auto result = transition_property(ts, properties, test_solver_factory(), msg);

  REQUIRE(result.properties.front().is_inconclusive());
}

SCENARIO("transition property: next-state predicate implied by transition")
{
  // s' = true, property: always next(s)
  // The transition relation forces s' = true, so X(s) holds.
  auto s = symbol_exprt{"s", bool_typet()};
  auto ts = make_transition_system("s", true_exprt());
  auto property_expr = sva_always_exprt{sva_ranged_always_exprt{
    natural_typet{}.one_expr(), natural_typet{}.one_expr(), s, bool_typet{}}};
  auto properties = make_properties(property_expr);
  null_message_handlert msg;

  auto result = transition_property(ts, properties, test_solver_factory(), msg);

  REQUIRE(result.properties.front().is_proved());
}

SCENARIO("transition property: tautological state predicate")
{
  // s' = s, property: always (s | !s)
  // Tautology, should be proved.
  auto s = symbol_exprt{"s", bool_typet()};
  auto ts = make_transition_system("s", s);
  auto properties =
    make_properties(sva_always_exprt{or_exprt{s, not_exprt{s}}});
  null_message_handlert msg;

  auto result = transition_property(ts, properties, test_solver_factory(), msg);

  REQUIRE(result.properties.front().is_proved());
}

SCENARIO("transition property: G(s -> X s) on identity transition")
{
  // s' = s, property: always (s -> X s)
  // If s is true now, it stays true. Should be proved.
  auto s = symbol_exprt{"s", bool_typet()};
  auto ts = make_transition_system("s", s);
  auto Xs = sva_ranged_always_exprt{
    natural_typet{}.one_expr(), natural_typet{}.one_expr(), s, bool_typet{}};
  auto property_expr = sva_always_exprt{implies_exprt{s, Xs}};
  auto properties = make_properties(property_expr);
  null_message_handlert msg;

  auto result = transition_property(ts, properties, test_solver_factory(), msg);

  REQUIRE(result.properties.front().is_proved());
}

SCENARIO("transition property: G(s -> X s) on toggle transition")
{
  // s' = !s, property: always (s -> X s)
  // If s is true, next s is false. Should be inconclusive.
  auto s = symbol_exprt{"s", bool_typet()};
  auto ts = make_transition_system("s", not_exprt{s});
  auto Xs = sva_ranged_always_exprt{
    natural_typet{}.one_expr(), natural_typet{}.one_expr(), s, bool_typet{}};
  auto property_expr = sva_always_exprt{implies_exprt{s, Xs}};
  auto properties = make_properties(property_expr);
  null_message_handlert msg;

  auto result = transition_property(ts, properties, test_solver_factory(), msg);

  REQUIRE(result.properties.front().is_inconclusive());
}

SCENARIO("transition property: unsupported liveness property")
{
  // property: F(s) — not of the form G(body)
  auto s = symbol_exprt{"s", bool_typet()};
  auto ts = make_transition_system("s", s);
  auto properties = make_properties(F_exprt{s});
  null_message_handlert msg;

  auto result = transition_property(ts, properties, test_solver_factory(), msg);

  REQUIRE(result.properties.front().is_unsupported());
}
