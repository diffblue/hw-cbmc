module main;

  // The base type of an enum may depend on an elaboration-time constant.
  typedef enum bit [p:1] { A } enum_t;

  parameter p = 8;

  // expected to pass
  p1: assert final ($bits(A) == p);

endmodule
