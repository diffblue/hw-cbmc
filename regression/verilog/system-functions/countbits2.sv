module main;

  // $countbits with multiple control bits
  // Per IEEE 1800-2017 section 20.9

  // count both ones and zeros (should equal bit width)
  p0: assert final ($countbits(8'b10101010, '0, '1) == 8);

  // count x and z bits in a four-state value
  p1: assert final ($countbits(4'b01xz, 'x, 'z) == 2);

  // count x bits only
  p2: assert final ($countbits(4'b01xz, 'x) == 1);

  // count z bits only
  p3: assert final ($countbits(4'b01xz, 'z) == 1);

  // $countbits yields an elaboration-time constant
  parameter P = 8'b11001100;
  parameter Q = $countbits(P, '1);

endmodule
