module main;

  typedef union packed {
    logic [6:0] field1;
    logic [6:0] field2;
  } u_t;

  // an assignment pattern
  wire u_t u = '{ field2: 3 };

  // Expected to pass.
  p0: assert property (u.field1 == 3);

endmodule
