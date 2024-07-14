module main;

  parameter B = A + 1;

  enum { A = 1, C = B + 1 } my_enum;

  // expected to pass
  pA: assert final (A == 1);
  pB: assert final (B == 2);
  pC: assert final (C == 3);

endmodule
