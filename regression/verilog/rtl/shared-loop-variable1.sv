// A module-level 'integer' loop counter shared by two clocked always
// blocks must not be reported as a driver conflict: integers are
// elaboration-only scratch, not state, so reusing the same counter across
// blocks is benign -- only the loop bodies' assignments to real state
// (a, b below) matter.
// Regression for LogikBench blocks/chiplink (signal i, chiplink_rx.v).
// Both outputs are clocked here; see shared-loop-variable2.sv (two
// combinational blocks) and shared-loop-variable3.sv (combinational and
// clocked) for the sibling cases.
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
