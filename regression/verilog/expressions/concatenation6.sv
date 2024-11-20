module main;

  typedef enum { RED, YELLOW1, GREEN, YELLOW2 } my_enum;

  // enums are allowed in concatenations
  wire [63:0] x = { RED, YELLOW1 };

  assert final (x == {32'd0, 32'd1});

endmodule
