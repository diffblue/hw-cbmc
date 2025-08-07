/*******************************************************************\

Module: Hanoi Omega Automata (HOA) Format

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <temporal-logic/hoa.h>
#include <testing-utils/use_catch.h>

SCENARIO("Parsing a HOA from a string")
{
  GIVEN("A HOA string for Xp")
  {
    auto hoa_string =
      "HOA: v1.1\n"
      "name: X!a0\n"
      "States: 4\n"
      "Start: 1\n"
      "AP: 1 a0\n"
      "acc-name: Buchi\n"
      "Acceptance: 1 Inf ( 0 )\n"
      "properties: trans-labels explicit-labels state-acc complete\n"
      "properties: deterministic terminal very-weak\n"
      "--BODY--\n"
      "State: 0 {0}\n"
      "[!0] 2\n"
      "[0] 3\n"
      "State: 1 {0}\n"
      "[t] 0\n"
      "State: 2 {0}\n"
      "[t] 2\n"
      "State: 3\n"
      "[t] 3\n"
      "--END--\n";

    auto hoa = hoat::from_string(hoa_string);

    REQUIRE(hoa.body.size() == 4);

    REQUIRE(hoa.body[0].first.is_accepting());
    REQUIRE(hoa.body[1].first.is_accepting());
    REQUIRE(hoa.body[2].first.is_accepting());
    REQUIRE(!hoa.body[3].first.is_accepting());

    // now remove the extra accepting states
    hoa.buechi_acceptance_cleanup();

    REQUIRE(!hoa.body[0].first.is_accepting());
    REQUIRE(!hoa.body[1].first.is_accepting());
    REQUIRE(hoa.body[2].first.is_accepting());
    REQUIRE(!hoa.body[3].first.is_accepting());
  }
}
