module main;

  union packed {
    bit [6:0] field1;
    bit [6:0] field2;
  } u;

  initial u.field1 = 7'b1010101;

  // Packed unions can be treated like bit-vectors.
  // Expected to pass.
  p0: assert property ($bits(u) == 7);
  p1: assert property (u == 7'b1010101);
  p2: assert property (u[1] == 0);

endmodule
