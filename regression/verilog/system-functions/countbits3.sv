module main;

  // If a control_bit value has a width greater than 1, only the LSB is used.
  // Per IEEE 1800-2017 section 20.9

  // 2'b01 has LSB = 1, so this counts ones
  p0: assert final ($countbits(8'b10101010, 2'b01) == 4);

  // 2'b10 has LSB = 0, so this counts zeros
  p1: assert final ($countbits(8'b10101010, 2'b10) == 4);

  // 4'b0110 has LSB = 0, so this counts zeros
  p2: assert final ($countbits(8'b11110000, 4'b0110) == 4);

endmodule
