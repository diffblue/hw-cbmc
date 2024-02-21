module main;

  typedef enum bit [7:0] { A = 'h0101 } enum_t;

  // expected to pass
  p1: assert property (A == enum_t'(1));

endmodule
