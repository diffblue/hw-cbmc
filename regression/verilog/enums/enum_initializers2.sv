module main;

  parameter B = A + 1;

  enum { A = 1, C = B + 1 } my_enum;

  // expected to pass
  pA: assert property (A == 1);
  pB: assert property (B == 2);
  pC: assert property (C == 3);

endmodule
