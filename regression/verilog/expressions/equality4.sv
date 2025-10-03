module main;

  // The two operands are zero-extended to 8 bits.
  initial assert((2'b10 + 1'sbx) === 8'bxxxxxxxx);
  initial assert((2'b10 | 1'sbx) === 8'b0000001x);

endmodule
