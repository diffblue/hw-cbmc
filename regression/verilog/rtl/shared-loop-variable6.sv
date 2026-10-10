// Correctness hole introduced by the type-based exemption: a variable
// declared 'integer' that is genuine two-driver STATE (written by two
// separate clocked blocks and read elsewhere) is a real multiple-driver
// conflict and should be rejected. But because the exemption in
// verilog_rtl_buildert::commit (src/verilog/verilog_rtl.cpp) suppresses
// the multiple-driver check for every 'integer'-typed symbol -- not only
// for loop counters that are dead outside their block -- this conflict is
// now silently accepted, producing a (last-writer-wins) model rather than
// an honest error.
// Desired behaviour: rejected with "has multiple drivers" / CONVERSION
// ERROR, as for a non-'integer' register driven by two clocked blocks.
// A liveness-based exemption (index dead outside the writing block) would
// not mask this, because 'count' is read by the third block.
module main(input clk, output reg [3:0] o);

  integer count;

  initial count = 0;

  always @(posedge clk) count = count + 1;  // driver 1
  always @(posedge clk) count = count + 2;  // driver 2

  always @(posedge clk) o <= count[3:0];    // reads 'count' as state

  p0: assert final (o == 4'd0);

endmodule
