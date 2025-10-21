module main;

  // base 2
  pA0: assert final ('sb1 == -1);
  pA1: assert final ('sb01 == 1);
  pA2: assert final ('sb1x === 'sb1111111111111111111111111111111x);
  pA3: assert final ($bits('sb1) == 32);
  pA4: assert final ('sb11 == -1);
  pA5: assert final (4'sb111 == 7);
  pA6: assert final ($bits(4'sb111) == 4);

  // base 8
  pB0: assert final ('so7 == -1);
  pB1: assert final ('so1 == 1);
  pB2: assert final ('so7x === 32'so3777777777x);
  pB3: assert final ($bits('so1) == 32);
  pB4: assert final ('so77 == -1);
  pB5: assert final (4'so7 == 7);
  pB6: assert final ($bits(4'so7) == 4);

  // base 16
  pC0: assert final ('shf == -1);
  pC1: assert final ('sh1 == 1);
  pC2: assert final ('shfx === 'shfffffffx);
  pC3: assert final ($bits('sh1) == 32);
  pC4: assert final ('shff == -1);
  pC5: assert final (8'shf == 15);
  pC6: assert final ($bits(8'shf) == 8);

endmodule
