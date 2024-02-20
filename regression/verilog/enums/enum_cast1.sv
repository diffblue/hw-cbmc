module main;

  typedef enum { A = 1, B = 2 } enum_t;

  // expected to pass
  p1: assert property (A == enum_t'(1));
  p2: assert property (B == enum_t'(2));

endmodule
