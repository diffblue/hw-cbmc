/*******************************************************************\

Module: RTL Representation Unit Tests

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/cout_message.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <testing-utils/use_catch.h>
#include <verilog/verilog_elaborate_compilation_unit.h>
#include <verilog/verilog_parser.h>
#include <verilog/verilog_rtl.h>
#include <verilog/verilog_typecheck.h>

#include <sstream>

/// parse, elaborate and type check the given module source,
/// which is expected to contain a module 'main'
static symbol_tablet compile(const std::string &source)
{
  console_message_handlert message_handler;
  std::istringstream in(source);

  verilog_scopest scopes;
  verilog_parsert parser{verilog_standardt::SV2023, scopes, message_handler};
  parser.set_file("verilog_rtl_test.sv");
  parser.in = &in;
  parser.grammar = verilog_parsert::LANGUAGE;
  verilog_scanner_init();

  REQUIRE(!parser.parse());
  parser.parse_tree.build_item_map();

  symbol_tablet symbol_table;
  verilog_elaborate_compilation_unit(
    parser.parse_tree, false, symbol_table, message_handler);

  REQUIRE(!verilog_typecheck(
    symbol_table,
    "Verilog::main",
    verilog_standardt::SV2023,
    false,
    message_handler));

  return symbol_table;
}

/// construct the RTL representation for module 'main'
static verilog_rtlt rtl_of(const std::string &source)
{
  auto symbol_table = compile(source);
  console_message_handlert message_handler;
  return verilog_rtl(
    symbol_table, "Verilog::main", verilog_standardt::SV2023, message_handler);
}

SCENARIO("RTL slices")
{
  GIVEN("two disjoint slices")
  {
    verilog_rtl_slicet a{0, 3}, b{4, 7};
    REQUIRE(!a.overlaps(b));
    REQUIRE(!b.overlaps(a));
    REQUIRE(a < b);
    REQUIRE(a.width() == 4);
  }

  GIVEN("two overlapping slices")
  {
    verilog_rtl_slicet a{0, 4}, b{4, 7};
    REQUIRE(a.overlaps(b));
    REQUIRE(b.overlaps(a));
  }
}

SCENARIO("RTL construction for a register")
{
  GIVEN("a clocked always block")
  {
    auto rtl = rtl_of(
      "module main(input clk, input d, output reg q);\n"
      "  always @(posedge clk) q <= d;\n"
      "endmodule\n");

    THEN("q is a state-holding slice defined by d")
    {
      REQUIRE(rtl.identifier_map.size() == 1);

      auto q_it = rtl.identifier_map.find("Verilog::$root.main.q");
      REQUIRE(q_it != rtl.identifier_map.end());
      REQUIRE(q_it->second.size() == 1);

      auto &slice = q_it->second.begin()->first;
      auto &definition = q_it->second.begin()->second;

      REQUIRE(slice == verilog_rtl_slicet{0, 0});
      REQUIRE(definition.is_state_holding());
      REQUIRE(!definition.is_wire());
      REQUIRE(definition.value.id() == ID_symbol);
      REQUIRE(
        to_symbol_expr(definition.value).get_identifier() ==
        "Verilog::$root.main.d");
    }
  }
}

SCENARIO("RTL construction for a wire")
{
  GIVEN("a continuous assignment")
  {
    auto rtl = rtl_of(
      "module main(input a, input b, output w);\n"
      "  assign w = a & b;\n"
      "endmodule\n");

    THEN("w is a wire defined by a & b")
    {
      auto w_it = rtl.identifier_map.find("Verilog::$root.main.w");
      REQUIRE(w_it != rtl.identifier_map.end());
      REQUIRE(w_it->second.size() == 1);

      auto &slice = w_it->second.begin()->first;
      auto &definition = w_it->second.begin()->second;

      REQUIRE(slice == verilog_rtl_slicet{0, 0});
      REQUIRE(definition.is_wire());
      REQUIRE(!definition.is_state_holding());
      REQUIRE(definition.value.id() == ID_and);
    }
  }
}

SCENARIO("RTL construction with part selects")
{
  GIVEN("assignments to two disjoint part selects of a register")
  {
    auto rtl = rtl_of(
      "module main(input clk, input [3:0] d, output reg [7:0] q);\n"
      "  always @(posedge clk) begin\n"
      "    q[3:0] <= d;\n"
      "    q[7:4] <= ~d;\n"
      "  end\n"
      "endmodule\n");

    THEN("q has two state-holding slices")
    {
      auto q_it = rtl.identifier_map.find("Verilog::$root.main.q");
      REQUIRE(q_it != rtl.identifier_map.end());
      REQUIRE(q_it->second.size() == 2);

      auto slice_it = q_it->second.begin();
      REQUIRE(slice_it->first == verilog_rtl_slicet{0, 3});
      REQUIRE(slice_it->second.is_state_holding());
      REQUIRE(slice_it->second.value.id() == ID_symbol);

      ++slice_it;
      REQUIRE(slice_it->first == verilog_rtl_slicet{4, 7});
      REQUIRE(slice_it->second.is_state_holding());
    }
  }

  GIVEN("an assignment to a bit select")
  {
    auto rtl = rtl_of(
      "module main(input clk, input d, output reg [7:0] q);\n"
      "  always @(posedge clk) q[2] <= d;\n"
      "endmodule\n");

    THEN("only bit 2 of q is defined")
    {
      auto q_it = rtl.identifier_map.find("Verilog::$root.main.q");
      REQUIRE(q_it != rtl.identifier_map.end());
      REQUIRE(q_it->second.size() == 1);
      REQUIRE(q_it->second.begin()->first == verilog_rtl_slicet{2, 2});
    }
  }
}

SCENARIO("RTL construction with conditionals")
{
  GIVEN("an if statement with both branches assigning")
  {
    auto rtl = rtl_of(
      "module main(input clk, input e, input d, output reg q);\n"
      "  always @(posedge clk)\n"
      "    if(e) q <= d; else q <= !d;\n"
      "endmodule\n");

    THEN("the next-state value of q is a conditional expression")
    {
      auto q_it = rtl.identifier_map.find("Verilog::$root.main.q");
      REQUIRE(q_it != rtl.identifier_map.end());
      REQUIRE(q_it->second.size() == 1);

      auto &definition = q_it->second.begin()->second;
      REQUIRE(definition.is_state_holding());
      REQUIRE(definition.value.id() == ID_if);
    }
  }

  GIVEN("an if statement without else branch")
  {
    auto rtl = rtl_of(
      "module main(input clk, input e, input d, output reg q);\n"
      "  always @(posedge clk)\n"
      "    if(e) q <= d;\n"
      "endmodule\n");

    THEN("the register holds its value in the else branch")
    {
      auto q_it = rtl.identifier_map.find("Verilog::$root.main.q");
      REQUIRE(q_it != rtl.identifier_map.end());

      auto &definition = q_it->second.begin()->second;
      REQUIRE(definition.is_state_holding());
      REQUIRE(definition.value.id() == ID_if);

      auto &if_expr = to_if_expr(definition.value);
      REQUIRE(if_expr.true_case().id() == ID_symbol);
      REQUIRE(
        to_symbol_expr(if_expr.true_case()).get_identifier() ==
        "Verilog::$root.main.d");
      REQUIRE(if_expr.false_case().id() == ID_symbol);
      REQUIRE(
        to_symbol_expr(if_expr.false_case()).get_identifier() ==
        "Verilog::$root.main.q");
    }
  }
}

SCENARIO("RTL construction with blocking assignments")
{
  GIVEN("a blocking assignment followed by a non-blocking assignment")
  {
    auto rtl = rtl_of(
      "module main(input clk, input a, output reg q);\n"
      "  reg t;\n"
      "  always @(posedge clk) begin\n"
      "    t = a;\n"
      "    q <= t;\n"
      "  end\n"
      "endmodule\n");

    THEN("the intermediate value is substituted into the next-state value")
    {
      auto q_it = rtl.identifier_map.find("Verilog::$root.main.q");
      REQUIRE(q_it != rtl.identifier_map.end());

      auto &q_definition = q_it->second.begin()->second;
      REQUIRE(q_definition.is_state_holding());
      REQUIRE(q_definition.value.id() == ID_symbol);
      REQUIRE(
        to_symbol_expr(q_definition.value).get_identifier() ==
        "Verilog::$root.main.a");

      // t itself is also state-holding
      auto t_it = rtl.identifier_map.find("Verilog::$root.main.t");
      REQUIRE(t_it != rtl.identifier_map.end());
      REQUIRE(t_it->second.begin()->second.is_state_holding());
    }
  }
}
