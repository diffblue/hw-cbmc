module main;

  union packed {
    bit [6:0] field1;
    bit [6:0] field2;
  } u;

  // bit-vectors can be converted without cast to packed unions
  initial u = 7'b1010101;

  // Expected to pass.
  p0: assert property ($bits(u) == 7);
  p1: assert property (u.field1 == 7'b1010101);
  p2: assert property (u.field2 == 7'b1010101);

endmodule
