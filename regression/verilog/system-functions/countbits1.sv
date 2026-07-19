module main;

  // $countbits counts the number of bits matching the control bit(s)
  // Per IEEE 1800-2017 section 20.9

  // count ones
  p0: assert final ($countbits(8'b10101010, '1) == 4);

  // count zeros
  p1: assert final ($countbits(8'b10101010, '0) == 4);

  // count ones in all-ones
  p2: assert final ($countbits(8'b11111111, '1) == 8);

  // count ones in all-zeros
  p3: assert final ($countbits(8'b00000000, '1) == 0);

  // count zeros in all-zeros
  p4: assert final ($countbits(8'b00000000, '0) == 8);

endmodule
