module main;

  // expected to fail typecheck owing to cycle
  parameter B = A;
  enum { A = B } my_enum;

endmodule
