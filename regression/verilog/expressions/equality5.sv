module main;

  // The two operands are sign-extended to 8 bits.
  initial assert((2'sb10 + 1'sbx) === 8'sbxxxxxxxx);
  initial assert((2'sb10 | 1'sbx) === 8'sb1111111x);

endmodule
