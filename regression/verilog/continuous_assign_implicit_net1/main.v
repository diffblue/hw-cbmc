// An undeclared identifier used as a member of a concatenation on the LHS
// of a continuous assignment is implicitly declared as a scalar net of the
// default net type (IEEE 1800-2017 6.10). Here `cout` is never declared;
// it is the discarded carry-out of the subtraction.
// Regression for LogikBench arithmetic/sub.
module main #(parameter DW = 16)
  (
   input [DW-1:0]  a,
   input [DW-1:0]  b,
   output [DW-1:0] out
   );

  assign {cout, out[DW-1:0]} = a[DW-1:0] - b[DW-1:0];

endmodule
