/*******************************************************************\

Module: LTL to CTL Unit Tests

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <temporal-logic/ctl.h>
#include <temporal-logic/ltl.h>
#include <temporal-logic/temporal_logic.h>
#include <testing-utils/use_catch.h>

SCENARIO("LTL_to_CTL accepts the supported fragment")
{
  auto p = symbol_exprt{"p", bool_typet{}};
  auto q = symbol_exprt{"q", bool_typet{}};
  auto r = symbol_exprt{"r", bool_typet{}};
  auto s = symbol_exprt{"s", bool_typet{}};

  THEN("Fp maps to AFp")
  {
    auto ctl = LTL_to_CTL(F_exprt{p});
    REQUIRE(ctl.has_value());
    REQUIRE(*ctl == AF_exprt{p});
  }

  THEN("Gp maps to AGp")
  {
    auto ctl = LTL_to_CTL(G_exprt{p});
    REQUIRE(ctl.has_value());
    REQUIRE(*ctl == AG_exprt{p});
  }

  THEN("Xp maps to AXp")
  {
    auto ctl = LTL_to_CTL(X_exprt{p});
    REQUIRE(ctl.has_value());
    REQUIRE(*ctl == AX_exprt{p});
  }

  THEN("GFp maps to AGAFp")
  {
    auto ctl = LTL_to_CTL(G_exprt{F_exprt{p}});
    REQUIRE(ctl.has_value());
    REQUIRE(*ctl == AG_exprt{AF_exprt{p}});
  }

  THEN("conjunction is mapped componentwise")
  {
    auto ctl = LTL_to_CTL(and_exprt{G_exprt{p}, F_exprt{q}});
    REQUIRE(ctl.has_value());
    REQUIRE(*ctl == and_exprt{AG_exprt{p}, AF_exprt{q}});
  }

  THEN("guarded or maps to a state formula")
  {
    auto ltl = or_exprt{and_exprt{p, X_exprt{q}}, and_exprt{not_exprt{p}, r}};
    auto ctl = LTL_to_CTL(ltl);
    REQUIRE(ctl.has_value());
    REQUIRE(
      *ctl == or_exprt{and_exprt{p, AX_exprt{q}}, and_exprt{not_exprt{p}, r}});
  }

  THEN("guarded until maps to AU")
  {
    auto ltl = U_exprt{and_exprt{p, X_exprt{q}}, and_exprt{not_exprt{p}, r}};
    auto ctl = LTL_to_CTL(ltl);
    REQUIRE(ctl.has_value());
    REQUIRE(
      *ctl == AU_exprt{and_exprt{p, AX_exprt{q}}, and_exprt{not_exprt{p}, r}});
  }

  THEN("guarded weak until maps to AR")
  {
    auto ltl =
      weak_U_exprt{and_exprt{p, X_exprt{q}}, and_exprt{not_exprt{p}, r}};
    auto ctl = LTL_to_CTL(ltl);
    REQUIRE(ctl.has_value());
    REQUIRE(
      *ctl ==
      AR_exprt{
        and_exprt{not_exprt{p}, r},
        or_exprt{and_exprt{p, AX_exprt{q}}, and_exprt{not_exprt{p}, r}}});
  }

  THEN("nested supported formulas remain supported")
  {
    auto ltl = G_exprt{
      or_exprt{and_exprt{p, X_exprt{q}}, and_exprt{not_exprt{p}, F_exprt{s}}}};
    auto ctl = LTL_to_CTL(ltl);
    REQUIRE(ctl.has_value());
    REQUIRE(
      *ctl ==
      AG_exprt{or_exprt{
        and_exprt{p, AX_exprt{q}}, and_exprt{not_exprt{p}, AF_exprt{s}}}});
  }
}

SCENARIO("LTL_to_CTL rejects formulas outside the common fragment")
{
  auto p = symbol_exprt{"p", bool_typet{}};
  auto q = symbol_exprt{"q", bool_typet{}};

  THEN("FGp is rejected")
  {
    REQUIRE(!LTL_to_CTL(F_exprt{G_exprt{p}}).has_value());
  }

  THEN("FXXp is rejected")
  {
    REQUIRE(!LTL_to_CTL(F_exprt{X_exprt{X_exprt{p}}}).has_value());
  }

  THEN("non-guarded disjunction is rejected")
  {
    REQUIRE(!LTL_to_CTL(or_exprt{X_exprt{p}, q}).has_value());
  }

  THEN("non-guarded until is rejected")
  {
    REQUIRE(!LTL_to_CTL(U_exprt{X_exprt{p}, q}).has_value());
  }
}
