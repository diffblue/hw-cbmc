module main;

  typedef enum bit [7:0] { A } enum_t;

  // expected to pass
  p1: assert final ($bits(A) == 8);

endmodule
