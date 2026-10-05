// An assertion placed *after* a for loop whose body contains a `break`
// must be checked normally: the `break` only terminates the loop, it does
// not make the code following the loop unreachable (IEEE 1800-2017,
// section 12.8 "Jump statements": `break` terminates the execution of the
// loop and continues with the statement following the loop).
//
// Here the loop always runs (i goes 0,1 then breaks at i==2), so after the
// loop `p0: assert(0)` is reached on every clock cycle and must be REFUTED.
//
// KNOWNBUG: the RTL builder (verilog_rtl_buildert::build_statement in
// src/verilog/verilog_rtl.cpp) implements `break` by pushing false_exprt
// onto state.guard to kill the rest of the path. When the enclosing `if`
// has a constant condition, build_if executes the branch directly on
// `state` and the dead (false) guard is never popped, so it stays active
// after the loop and makes the assertion vacuously PROVED.
module main(input clk);
  reg [3:0] x = 0;
  always @(posedge clk) begin
    for (int i = 0; i < 4; i++) begin
      if (i == 2) break;
      x = x + 1;
    end
    p0: assert (0); // reached every cycle -> must be REFUTED
  end
endmodule
