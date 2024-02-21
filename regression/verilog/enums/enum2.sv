module main;

  enum { A, B } ab = A;
  enum { C, D } cd = A; // expected to fail typecheck

endmodule
