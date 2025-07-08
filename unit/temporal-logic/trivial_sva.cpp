/*******************************************************************\

Module: Trivial SVA

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <temporal-logic/trivial_sva.h>
#include <testing-utils/use_catch.h>
#include <verilog/sva_expr.h>

SCENARIO("Simplifying a trivial SVA formula")
{
  auto p = symbol_exprt{"p", bool_typet{}};
  auto q = symbol_exprt{"q", bool_typet{}};
  auto r = symbol_exprt{"r", bool_typet{}};

  GIVEN("A trivial SVA formula with properties")
  {
    auto prop = [](exprt expr) {
      return sva_boolean_exprt{std::move(expr), bool_typet{}};
    };

    REQUIRE(trivial_sva(sva_not_exprt{prop(p)}) == not_exprt{prop(p)});
    REQUIRE(
      trivial_sva(
        sva_not_exprt{sva_and_exprt{prop(p), prop(q), bool_typet{}}}) ==
      not_exprt{and_exprt{prop(p), prop(q)}});
    REQUIRE(
      trivial_sva(
        sva_and_exprt{sva_not_exprt{prop(p)}, prop(q), bool_typet{}}) ==
      and_exprt{not_exprt{prop(p)}, prop(q)});
    REQUIRE(
      trivial_sva(sva_and_exprt{
        sva_or_exprt{prop(p), prop(q), bool_typet{}}, prop(r), bool_typet{}}) ==
      and_exprt{or_exprt{prop(p), prop(q)}, prop(r)});
  }

  GIVEN("A trivial SVA formula with sequences")
  {
    auto sequence_type = verilog_sva_sequence_typet{};
    auto seq = [](exprt expr) {
      return sva_boolean_exprt{std::move(expr), verilog_sva_sequence_typet{}};
    };

    auto weak = [](const exprt &expr) {
      return sva_weak_exprt{ID_sva_weak, expr};
    };

    REQUIRE(trivial_sva(weak(seq(p))) == p);

    REQUIRE(
      trivial_sva(weak(sva_and_exprt{
        sva_and_exprt{seq(p), seq(q), sequence_type}})) == and_exprt{p, q});

    REQUIRE(
      trivial_sva(weak(sva_and_exprt{sva_and_exprt{
        seq(p),
        sva_or_exprt{seq(q), seq(r), sequence_type},
        sequence_type}})) == and_exprt{p, or_exprt{q, r}});
  }
}
