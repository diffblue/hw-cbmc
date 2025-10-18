module main;

  // The arguments of === are adjusted to the maximum of the
  // self-determined widths of the lhs and rhs.
  // Hence, 4'b1111 << 1 is equal both to 4'b1110 and 5'b11110.
  assert final (4'b1111 << 1 === 4'b1110);
  assert final (4'b1111 << 1 === 5'b11110);

  assert final (1'b1 << 6 === 64);
  assert final (1'b1 << 6 === 1'b0);

  // The shift will have 16 bits!
  initial assert(8'b0 + (1'sb1 << 15) === 16'b1000_0000_0000_0000);

endmodule
