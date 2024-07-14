module main;

  enum { A = 1, B = A + 10 } my_enum;

  // expected to pass
  pA: assert final (A == 1);
  pB: assert final (B == 11);

endmodule
