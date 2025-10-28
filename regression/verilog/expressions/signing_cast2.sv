module main;

  // four-valued signing cast
  initial assert (signed'(4'b11xx) === 8'sb1111_11xx);
  initial assert (signed'(4'bx000) === 8'sbxxxx_x000);

  // four-valued signing cast
  initial assert (unsigned'(4'sb11xx) === 8'b0000_11xx);
  initial assert (unsigned'(4'sbx000) === 8'b0000_x000);

endmodule
