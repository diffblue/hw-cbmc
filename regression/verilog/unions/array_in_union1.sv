module main;

  union packed {
    bit array[4];
    bit [3:0] as_vector;
  } u;

  initial u.array = '{ 1, 1, 0, 1 };

  // Expected to pass.
  p0: assert final ($bits(u) == 4);
  p11: assert property (u.array[0] == 1);
  p12: assert property (u.array[1] == 1);
  p13: assert property (u.array[2] == 0);
  p14: assert property (u.array[3] == 1);
  p21: assert property (u.as_vector == 4'b1011);

endmodule
