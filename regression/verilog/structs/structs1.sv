module main;

  // The first field is the most-significant bit.
  struct packed {
    bit field1, field2;
    bit [6:0] field3;
  } s;

  // bit-vectors can be converted without cast to packed structs
  initial s = 8'b1011111;

  // Expected to pass.
  p0: assert property ($bits(s) == 9);
  p1: assert property (s.field1 == 1);
  p2: assert property (s.field2 == 0);
  p3: assert property (s.field3 == 'b111111);

endmodule
