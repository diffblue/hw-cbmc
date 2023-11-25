module main;

  enum { A = 1, B = A + 10 } my_enum;

  // expected to pass
  pA: assert property (A == 1);
  pB: assert property (B == 11);

endmodule
