module main;

  parameter B = A + 1;

  enum { A = 1, C = my_parameter + 1 } my_enum;

  // expected to pass
  pA: assert property (A == 1);
  pB: assert property (B == 2);
  pC: assert property (B == 3);

endmodule
