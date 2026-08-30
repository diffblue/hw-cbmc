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

/// strip reinterpret casts
static const exprt &peel_typecasts(const exprt &expr)
{
  if(expr.id() == ID_typecast)
    return peel_typecasts(to_typecast_expr(expr).op());
  else
    return expr;
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

SCENARIO("RTL construction with case statements")
{
  GIVEN("a case statement with a default")
  {
    auto rtl = rtl_of(
      "module main(input clk, input [1:0] sel, input d, output reg q);\n"
      "  always @(posedge clk)\n"
      "    case(sel)\n"
      "      2'b00: q <= d;\n"
      "      2'b01: q <= !d;\n"
      "      default: q <= 0;\n"
      "    endcase\n"
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

  GIVEN("a case statement without a default")
  {
    auto rtl = rtl_of(
      "module main(input clk, input [1:0] sel, input d, output reg q);\n"
      "  always @(posedge clk)\n"
      "    case(sel)\n"
      "      2'b00: q <= d;\n"
      "    endcase\n"
      "endmodule\n");

    THEN("the register holds its value if no case item matches")
    {
      auto q_it = rtl.identifier_map.find("Verilog::$root.main.q");
      REQUIRE(q_it != rtl.identifier_map.end());

      auto &definition = q_it->second.begin()->second;
      REQUIRE(definition.is_state_holding());
      REQUIRE(definition.value.id() == ID_if);

      auto &if_expr = to_if_expr(definition.value);
      REQUIRE(if_expr.false_case().id() == ID_symbol);
      REQUIRE(
        to_symbol_expr(if_expr.false_case()).get_identifier() ==
        "Verilog::$root.main.q");
    }
  }
}

SCENARIO("RTL construction with increment and decrement")
{
  GIVEN("an increment statement in a clocked always block")
  {
    auto rtl = rtl_of(
      "module main(input clk);\n"
      "  reg [3:0] count;\n"
      "  always @(posedge clk) count++;\n"
      "endmodule\n");

    THEN("the next-state value of the counter is a sum")
    {
      auto count_it = rtl.identifier_map.find("Verilog::$root.main.count");
      REQUIRE(count_it != rtl.identifier_map.end());
      REQUIRE(count_it->second.size() == 1);

      auto &definition = count_it->second.begin()->second;
      REQUIRE(definition.is_state_holding());
      REQUIRE(definition.value.id() == ID_plus);
    }
  }
}

SCENARIO("RTL construction with assertions")
{
  GIVEN("a guard-less always construct that contains a check only")
  {
    auto rtl = rtl_of(
      "module main(input clk, input d, output reg q);\n"
      "  always @(posedge clk) q <= d;\n"
      "  always assert p1: q == q;\n"
      "endmodule\n");

    THEN("the check does not contribute to the RTL representation")
    {
      REQUIRE(rtl.identifier_map.size() == 1);
      REQUIRE(
        rtl.identifier_map.find("Verilog::$root.main.q") !=
        rtl.identifier_map.end());
    }
  }

  GIVEN("an immediate assertion in a clocked always block")
  {
    auto rtl = rtl_of(
      "module main(input clk, input d, output reg q);\n"
      "  always @(posedge clk) begin\n"
      "    q <= d;\n"
      "    assert(d == d);\n"
      "  end\n"
      "endmodule\n");

    THEN("the assertion does not contribute to the RTL representation")
    {
      REQUIRE(rtl.identifier_map.size() == 1);

      auto q_it = rtl.identifier_map.find("Verilog::$root.main.q");
      REQUIRE(q_it != rtl.identifier_map.end());
      REQUIRE(q_it->second.begin()->second.is_state_holding());
    }
  }
}

SCENARIO("RTL construction with for loops")
{
  GIVEN("a for loop with constant bounds")
  {
    auto rtl = rtl_of(
      "module main(input [7:0] data, output reg is_zero);\n"
      "  reg [31:0] i;\n"
      "  always @data begin\n"
      "    is_zero = 1;\n"
      "    for(i = 0; i < 8; i = i + 1)\n"
      "      is_zero = is_zero && (data[i] == 0);\n"
      "  end\n"
      "endmodule\n");

    THEN("the loop is unrolled")
    {
      auto is_zero_it = rtl.identifier_map.find("Verilog::$root.main.is_zero");
      REQUIRE(is_zero_it != rtl.identifier_map.end());
      REQUIRE(is_zero_it->second.begin()->second.is_wire());

      // the loop variable ends at the loop bound
      auto i_it = rtl.identifier_map.find("Verilog::$root.main.i");
      REQUIRE(i_it != rtl.identifier_map.end());
      auto &i_value = i_it->second.begin()->second.value;
      REQUIRE(i_value.is_constant());
    }
  }

  GIVEN("a for loop with a break statement")
  {
    auto rtl = rtl_of(
      "module main(input [3:0] bits, output int index);\n"
      "  always_comb begin\n"
      "    for(index = 0; index < 4; index++)\n"
      "      if(bits[index])\n"
      "        break;\n"
      "  end\n"
      "endmodule\n");

    THEN("the result is a priority chain")
    {
      auto index_it = rtl.identifier_map.find("Verilog::$root.main.index");
      REQUIRE(index_it != rtl.identifier_map.end());
      REQUIRE(index_it->second.begin()->second.is_wire());
      REQUIRE(index_it->second.begin()->second.value.id() == ID_if);
    }
  }
}

SCENARIO("RTL construction with task enables")
{
  GIVEN("a task with input and output parameters")
  {
    auto rtl = rtl_of(
      "module main(input [31:0] x, output reg [31:0] y);\n"
      "  task some_task;\n"
      "    input [31:0] some_input;\n"
      "    output [31:0] some_output;\n"
      "    some_output = some_input+1;\n"
      "  endtask\n"
      "  always @x some_task(x, y);\n"
      "endmodule\n");

    THEN("the task is inlined, and its locals are not in the RTL")
    {
      REQUIRE(rtl.identifier_map.size() == 1);

      auto y_it = rtl.identifier_map.find("Verilog::$root.main.y");
      REQUIRE(y_it != rtl.identifier_map.end());
      REQUIRE(y_it->second.begin()->second.is_wire());
      REQUIRE(
        peel_typecasts(y_it->second.begin()->second.value).id() == ID_plus);
    }
  }
}

SCENARIO("RTL construction with concatenation lvalues")
{
  GIVEN("an assignment to a concatenation")
  {
    auto rtl = rtl_of(
      "module main(input [2:0] in, output reg [2:0] out);\n"
      "  always @in {out[2:1],out[0]} = in;\n"
      "endmodule\n");

    THEN("each part gets a slice of the right-hand side")
    {
      auto out_it = rtl.identifier_map.find("Verilog::$root.main.out");
      REQUIRE(out_it != rtl.identifier_map.end());
      REQUIRE(out_it->second.size() == 2);

      auto slice_it = out_it->second.begin();
      REQUIRE(slice_it->first == verilog_rtl_slicet{0, 0});
      ++slice_it;
      REQUIRE(slice_it->first == verilog_rtl_slicet{1, 2});
    }
  }
}

SCENARIO("RTL construction with struct members")
{
  GIVEN("continuous assignments to two members of a struct")
  {
    auto rtl = rtl_of(
      "module main;\n"
      "  typedef struct packed {\n"
      "    logic [31:0] f1, f2;\n"
      "  } my_struct;\n"
      "  wire my_struct s;\n"
      "  assign s.f1 = 1;\n"
      "  assign s.f2 = 2;\n"
      "endmodule\n");

    THEN(
      "the members are disjoint slices; the first member is "
      "the most significant")
    {
      auto s_it = rtl.identifier_map.find("Verilog::$root.main.s");
      REQUIRE(s_it != rtl.identifier_map.end());
      REQUIRE(s_it->second.size() == 2);

      auto slice_it = s_it->second.begin();
      REQUIRE(slice_it->first == verilog_rtl_slicet{0, 31}); // f2
      ++slice_it;
      REQUIRE(slice_it->first == verilog_rtl_slicet{32, 63}); // f1
    }
  }
}

SCENARIO("RTL construction with array elements")
{
  GIVEN("continuous assignments to two elements of an array")
  {
    auto rtl = rtl_of(
      "module main;\n"
      "  wire [7:0] array[0:1];\n"
      "  assign array[0] = 1;\n"
      "  assign array[1] = 2;\n"
      "endmodule\n");

    THEN("the elements are disjoint slices")
    {
      auto array_it = rtl.identifier_map.find("Verilog::$root.main.array");
      REQUIRE(array_it != rtl.identifier_map.end());
      REQUIRE(array_it->second.size() == 2);

      auto slice_it = array_it->second.begin();
      REQUIRE(slice_it->first == verilog_rtl_slicet{0, 7});
      ++slice_it;
      REQUIRE(slice_it->first == verilog_rtl_slicet{8, 15});
    }
  }

  GIVEN("an assignment to an array element with a non-constant index")
  {
    auto rtl = rtl_of(
      "module main(input clk, input [3:0] addr, input [7:0] data);\n"
      "  reg [7:0] mem[0:15];\n"
      "  always @(posedge clk) mem[addr] <= data;\n"
      "endmodule\n");

    THEN("the whole array is defined by a with-expression")
    {
      auto mem_it = rtl.identifier_map.find("Verilog::$root.main.mem");
      REQUIRE(mem_it != rtl.identifier_map.end());
      REQUIRE(mem_it->second.size() == 1);

      auto &definition = mem_it->second.begin()->second;
      REQUIRE(definition.is_state_holding());
      REQUIRE(definition.value.id() == ID_with);
    }
  }
}

SCENARIO("RTL construction with compound assignments")
{
  GIVEN("a compound assignment in a clocked always block")
  {
    auto rtl = rtl_of(
      "module main(input clk, input [7:0] d);\n"
      "  reg [7:0] acc;\n"
      "  always @(posedge clk) acc += d;\n"
      "endmodule\n");

    THEN("the next-state value of the accumulator is a sum")
    {
      auto acc_it = rtl.identifier_map.find("Verilog::$root.main.acc");
      REQUIRE(acc_it != rtl.identifier_map.end());

      auto &definition = acc_it->second.begin()->second;
      REQUIRE(definition.is_state_holding());
      REQUIRE(definition.value.id() == ID_plus);
    }
  }
}

SCENARIO("RTL construction with net declarations")
{
  GIVEN("a net declaration with a value")
  {
    auto rtl = rtl_of(
      "module main(input a, input b);\n"
      "  wire w = a ^ b;\n"
      "endmodule\n");

    THEN("the net is a wire in the RTL representation")
    {
      auto w_it = rtl.identifier_map.find("Verilog::$root.main.w");
      REQUIRE(w_it != rtl.identifier_map.end());
      REQUIRE(w_it->second.begin()->second.is_wire());
      REQUIRE(w_it->second.begin()->second.value.id() == ID_xor);
    }
  }
}

SCENARIO("RTL construction with properties")
{
  GIVEN("concurrent assert, assume and cover properties")
  {
    auto rtl = rtl_of(
      "module main(input clk, input a, input b);\n"
      "  p1: assert property (@(posedge clk) a |-> b);\n"
      "  assume property (@(posedge clk) a || b);\n"
      "  c1: cover property (@(posedge clk) b);\n"
      "endmodule\n");

    THEN("the properties are recorded in order, with labels when given")
    {
      REQUIRE(rtl.properties.size() == 3);

      REQUIRE(rtl.properties[0].is_assert());
      REQUIRE(rtl.properties[0].label == "p1");

      REQUIRE(rtl.properties[1].is_assume());
      REQUIRE(rtl.properties[1].label.empty());

      REQUIRE(rtl.properties[2].is_cover());
      REQUIRE(rtl.properties[2].label == "c1");
    }
  }

  GIVEN("an immediate assertion under a condition in an always block")
  {
    auto rtl = rtl_of(
      "module main(input clk, input a, input b);\n"
      "  reg q;\n"
      "  always @(posedge clk) begin\n"
      "    q <= a;\n"
      "    if(b)\n"
      "      a1: assert(q == a);\n"
      "  end\n"
      "endmodule\n");

    THEN(
      "the property is guarded by the path condition "
      "and carries the label")
    {
      REQUIRE(rtl.properties.size() == 1);
      REQUIRE(rtl.properties[0].is_assert());
      REQUIRE(rtl.properties[0].label == "a1");
      REQUIRE(rtl.properties[0].condition.id() == ID_verilog_implies);
    }
  }

  GIVEN("a guard-less always construct with a check")
  {
    auto rtl = rtl_of(
      "module main(input a);\n"
      "  always assert p1: a == a;\n"
      "endmodule\n");

    THEN("the check is recorded as a property")
    {
      REQUIRE(rtl.properties.size() == 1);
      REQUIRE(rtl.properties[0].is_assert());
      REQUIRE(rtl.properties[0].label == "p1");
      REQUIRE(rtl.properties[0].condition.id() == ID_equal);
    }
  }
}

SCENARIO("RTL construction with blocking assignments")
{
  GIVEN(
    "a blocking assignment to a part of a variable, "
    "followed by a read of the variable")
  {
    auto rtl = rtl_of(
      "module main(input clk, input [3:0] a, output reg [7:0] q);\n"
      "  reg [7:0] t;\n"
      "  always @(posedge clk) begin\n"
      "    t[3:0] = a;\n"
      "    q <= t;\n"
      "  end\n"
      "endmodule\n");

    THEN("the read composes the assigned slice with the current value")
    {
      auto q_it = rtl.identifier_map.find("Verilog::$root.main.q");
      REQUIRE(q_it != rtl.identifier_map.end());

      auto &q_definition = q_it->second.begin()->second;
      REQUIRE(q_definition.is_state_holding());

      // the value is a concatenation of t[7:4] and a
      auto value = q_definition.value;
      if(value.id() == ID_typecast)
        value = to_typecast_expr(value).op();
      REQUIRE(value.id() == ID_concatenation);
    }
  }

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
      REQUIRE(peel_typecasts(q_definition.value).id() == ID_symbol);
      REQUIRE(
        to_symbol_expr(peel_typecasts(q_definition.value)).get_identifier() ==
        "Verilog::$root.main.a");

      // t itself is also state-holding
      auto t_it = rtl.identifier_map.find("Verilog::$root.main.t");
      REQUIRE(t_it != rtl.identifier_map.end());
      REQUIRE(t_it->second.begin()->second.is_state_holding());
    }
  }
}
