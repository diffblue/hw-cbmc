// A module-level 'integer' loop counter shared by two clocked always
// blocks must not be reported as a driver conflict: integers are
// elaboration-only scratch, not state, so reusing the same counter across
// blocks is benign -- only the loop bodies' assignments to real state
// (a, b below) matter.
// Regression for LogikBench blocks/chiplink (signal i, chiplink_rx.v),
// which fails during RTL construction (--bound 0) rather than during
// combinational synthesis, unlike the sibling bug fixed for
// verilog_synthesis.cpp (shared-integer-loop-variable/two_combinational_blocks1.sv).
module main(input clk, input [3:0] din, output reg [3:0] a, output reg [3:0] b);

  integer i;

  always @(posedge clk)
    for (i = 0; i < 4; i = i + 1)
      a[i] <= din[i];

  always @(posedge clk)
    for (i = 0; i < 4; i = i + 1)
      b[i] <= ~din[i];

  p0: assert final (a == din);

endmodule
