module main;

  // As conditional_operator_short_circuit1.sv, but with the unevaluated
  // operand in the 'false' branch.  Per 1800-2017 11.4.11, 1/0 is not
  // evaluated, and hence the range is [2:0].
  wire [(1 ? 3 : 1/0)-1:0] x;

  initial assert ($bits(x) == 3);

endmodule
