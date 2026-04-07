/*******************************************************************\

Module: BDD Model Checker Unit Tests

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ebmc/bdd_model_checker.h>
#include <testing-utils/use_catch.h>

/// Build a simple transition system with a single Boolean variable s.
/// States: s=0 and s=1.
/// Transition: s always goes to !s (toggle).
/// No constraints.
static bdd_transition_relationt make_toggle_system(mini_bdd_mgrt &mgr)
{
  auto s = mgr.Var("s");
  auto s_next = mgr.Var("s'");

  bdd_transition_relationt tr;
  tr.variables.push_back({s, s_next});
  // next(s) = !s, encoded as s_next == !s
  tr.transition_conjuncts.push_back(s_next == !s);

  return tr;
}

/// Build a system with two Boolean variables: s0, s1.
/// Transition: next(s0) = s0 | s1, next(s1) = s0 ^ s1.
/// States and transitions:
///   (0,0) -> (0,0)  self-loop
///   (0,1) -> (1,1)
///   (1,0) -> (1,1)
///   (1,1) -> (1,0)
/// So (0,0) is absorbing, and {(1,0),(1,1)} form a cycle.
static bdd_transition_relationt make_counter_system(mini_bdd_mgrt &mgr)
{
  auto s0 = mgr.Var("s0");
  auto s1 = mgr.Var("s1");
  auto s0_next = mgr.Var("s0'");
  auto s1_next = mgr.Var("s1'");

  bdd_transition_relationt tr;
  tr.variables.push_back({s0, s0_next});
  tr.variables.push_back({s1, s1_next});
  tr.transition_conjuncts.push_back(s0_next == (s0 | s1));
  tr.transition_conjuncts.push_back(s1_next == (s0 ^ s1));

  return tr;
}

SCENARIO("BDD model checker EX on toggle system")
{
  mini_bdd_mgrt mgr;
  auto tr = make_toggle_system(mgr);
  auto s = tr.variables[0].current;
  bdd_model_checkert mc(tr);

  GIVEN("The set of states where s=1")
  {
    THEN("EX(s) gives states whose successor has s=1, i.e., s=0")
    {
      auto result = mc.EX(s);
      REQUIRE((result == !s).is_true());
    }
  }

  GIVEN("The set of states where s=0")
  {
    THEN("EX(!s) gives states whose successor has s=0, i.e., s=1")
    {
      auto result = mc.EX(!s);
      REQUIRE((result == s).is_true());
    }
  }
}

SCENARIO("BDD model checker AX on toggle system")
{
  mini_bdd_mgrt mgr;
  auto tr = make_toggle_system(mgr);
  auto s = tr.variables[0].current;
  bdd_model_checkert mc(tr);

  GIVEN("The toggle system is deterministic")
  {
    THEN("AX(s) equals EX(s)")
    {
      REQUIRE((mc.AX(s) == mc.EX(s)).is_true());
    }
  }
}

SCENARIO("BDD model checker EF on toggle system")
{
  mini_bdd_mgrt mgr;
  auto tr = make_toggle_system(mgr);
  auto s = tr.variables[0].current;
  bdd_model_checkert mc(tr);

  GIVEN("Any state can eventually reach s=1")
  {
    THEN("EF(s) is true for all states")
    {
      REQUIRE(mc.EF(s).is_true());
    }
  }

  GIVEN("Any state can eventually reach s=0")
  {
    THEN("EF(!s) is true for all states")
    {
      REQUIRE(mc.EF(!s).is_true());
    }
  }
}

SCENARIO("BDD model checker EG on toggle system")
{
  mini_bdd_mgrt mgr;
  auto tr = make_toggle_system(mgr);
  auto s = tr.variables[0].current;
  bdd_model_checkert mc(tr);

  GIVEN("s toggles every step")
  {
    THEN("EG(s) is false — s cannot stay true forever")
    {
      REQUIRE(mc.EG(s).is_false());
    }

    THEN("EG(true) is true — there is always a successor")
    {
      REQUIRE(mc.EG(mgr.True()).is_true());
    }
  }
}

SCENARIO("BDD model checker AG on toggle system")
{
  mini_bdd_mgrt mgr;
  auto tr = make_toggle_system(mgr);
  auto s = tr.variables[0].current;
  bdd_model_checkert mc(tr);

  GIVEN("s toggles every step")
  {
    THEN("AG(s) is false")
    {
      REQUIRE(mc.AG(s).is_false());
    }

    THEN("AG(true) is true")
    {
      REQUIRE(mc.AG(mgr.True()).is_true());
    }
  }
}

SCENARIO("BDD model checker AF on toggle system")
{
  mini_bdd_mgrt mgr;
  auto tr = make_toggle_system(mgr);
  auto s = tr.variables[0].current;
  bdd_model_checkert mc(tr);

  GIVEN("s toggles every step")
  {
    THEN("AF(s) is true — s will inevitably become true")
    {
      REQUIRE(mc.AF(s).is_true());
    }
  }
}

SCENARIO("BDD model checker EU on toggle system")
{
  mini_bdd_mgrt mgr;
  auto tr = make_toggle_system(mgr);
  auto s = tr.variables[0].current;
  bdd_model_checkert mc(tr);

  GIVEN("E[!s U s]")
  {
    THEN(
      "All states satisfy it — s=1 satisfies it immediately, "
      "s=0 reaches s=1 in one step")
    {
      REQUIRE(mc.EU(!s, s).is_true());
    }
  }

  GIVEN("E[false U s]")
  {
    THEN("Only states where s=1 satisfy it")
    {
      REQUIRE((mc.EU(mgr.False(), s) == s).is_true());
    }
  }
}

SCENARIO("BDD model checker AU on toggle system")
{
  mini_bdd_mgrt mgr;
  auto tr = make_toggle_system(mgr);
  auto s = tr.variables[0].current;
  bdd_model_checkert mc(tr);

  GIVEN("A[!s U s]")
  {
    THEN("All states satisfy it (deterministic, same as EU)")
    {
      REQUIRE(mc.AU(!s, s).is_true());
    }
  }
}

SCENARIO("BDD model checker ER on toggle system")
{
  mini_bdd_mgrt mgr;
  auto tr = make_toggle_system(mgr);
  auto s = tr.variables[0].current;
  bdd_model_checkert mc(tr);

  GIVEN("E[false R s] is equivalent to EG(s)")
  {
    THEN("Both are false on the toggle system")
    {
      REQUIRE((mc.ER(mgr.False(), s) == mc.EG(s)).is_true());
    }
  }
}

SCENARIO("BDD model checker AR on toggle system")
{
  mini_bdd_mgrt mgr;
  auto tr = make_toggle_system(mgr);
  auto s = tr.variables[0].current;
  bdd_model_checkert mc(tr);

  GIVEN("A[false R s] is equivalent to AG(s)")
  {
    THEN("Both are false on the toggle system")
    {
      REQUIRE((mc.AR(mgr.False(), s) == mc.AG(s)).is_true());
    }
  }
}

SCENARIO("BDD model checker on counter system with absorbing state")
{
  mini_bdd_mgrt mgr;
  auto tr = make_counter_system(mgr);
  auto s0 = tr.variables[0].current;
  auto s1 = tr.variables[1].current;
  bdd_model_checkert mc(tr);

  // Transitions:
  //   (0,0) -> (0,0)  absorbing
  //   (0,1) -> (1,1)
  //   (1,0) -> (1,1)
  //   (1,1) -> (1,0)
  // So (0,0) is a self-loop, and (1,0) <-> (1,1) is a cycle.

  GIVEN("State (0,0) is absorbing")
  {
    auto state_00 = !s0 & !s1;

    THEN("EG(!s0 & !s1) includes (0,0)")
    {
      auto eg = mc.EG(state_00);
      REQUIRE(!(eg & state_00).is_false());
    }

    THEN("AG(!s0) from (0,0) — s0 is always 0")
    {
      auto ag_not_s0 = mc.AG(!s0);
      REQUIRE(!(ag_not_s0 & state_00).is_false());
    }
  }

  GIVEN("State (0,1) eventually reaches s0=1")
  {
    auto state_01 = !s0 & s1;

    THEN("EF(s0) includes (0,1)")
    {
      auto ef = mc.EF(s0);
      REQUIRE(!(ef & state_01).is_false());
    }
  }
}

SCENARIO("BDD model checker with constraints")
{
  mini_bdd_mgrt mgr;
  auto tr = make_toggle_system(mgr);
  auto s = tr.variables[0].current;

  // Add constraint: s must be true (restricts to single state)
  tr.constraint_conjuncts.push_back(s);
  bdd_model_checkert mc(tr);

  GIVEN("Constraint restricts to s=1 states only")
  {
    THEN("EX(s) is false — the successor has s=0, which violates constraint")
    {
      REQUIRE(mc.EX(s).is_false());
    }
  }
}
