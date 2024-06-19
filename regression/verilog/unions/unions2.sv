module main;

  union {
    bit field1;
    bit [6:0] field2;
  } u;

  initial begin
    u.field2 = 0;
    u.field1 = 1;
  end

  // Expected to pass.
  p1: assert property (u.field1 == 1);
  p2: assert property (u.field2 == 1);
  p3: assert property ($bits(u) == 7);

endmodule
