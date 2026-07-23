// A module-level 'integer' loop counter shared by a combinational and a
// clocked always block must not be reported as "conflicting assignment
// types" (new: clocked, old: combinational): integers are elaboration-only
// scratch, not state, so the reuse is benign.
// Regression for LogikBench blocks/viterbi (signal j) and large/qr (k).
module main(input clk, input [3:0] din, output reg [3:0] a, output reg [3:0] b);
  integer i;
  always @(*)
    for (i = 0; i < 4; i = i + 1)
      a[i] = din[i];
  always @(posedge clk)
    for (i = 0; i < 4; i = i + 1)
      b[i] <= din[i];
  p0: assert final (a == din);
endmodule
