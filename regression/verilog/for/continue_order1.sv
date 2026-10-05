// Multiple conditional `continue` statements in a loop body.
// Per IEEE 1800-2017 section 12.8, `continue` jumps immediately to the end
// of the current loop iteration, so an earlier `continue` whose condition
// holds must take priority over any later statement, including a later
// `continue`. Here the single-iteration loop sets x = 0, and if c1 holds
// continues (leaving x == 0); only if !c1 does it reach x = 1 and the
// second `continue` on c2. Hence when c1 && c2 the result must be x == 0.
//
// KNOWNBUG: verilog_rtl_buildert::build_for in src/verilog/verilog_rtl.cpp
// merges the recorded `continue_states` in forward program order, so the
// later `continue` on c2 overrides the earlier one on c1. With --show-rtl
// the next-state is c2 ? 1 : (c1 ? 0 : 2) instead of the correct
// c1 ? 0 : (c2 ? 1 : 2), so when c1 && c2 the tool reports x == 1 and p0
// is REFUTED. Compare the correct, reverse-order merge of `break_states`
// in the same function.
module main(input clk, input c1, c2);

  reg [3:0] x;

  always @(posedge clk) begin
    for (int i = 0; i < 1; i++) begin
      x = 0;
      if (c1) continue;
      x = 1;
      if (c2) continue;
      x = 2;
    end
  end

  p0: assert property (@(posedge clk) (c1 && c2) |-> ##1 x == 0); // must be PROVED

endmodule
