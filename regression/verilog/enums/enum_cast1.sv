module main;

  typedef enum { A = 1, B = 2 } enum_t;

  // expected to pass
  p1: assert final (A == enum_t'(1));
  p2: assert final (B == enum_t'(2));

endmodule
