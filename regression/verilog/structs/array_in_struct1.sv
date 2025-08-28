module main;

  struct {
    // unpacked
    int array1[4];

    // packed
    bit [3:0] [31:0] array2;
  } s;

  initial s = '{ '{ 1, 2, 3, 4 }, '{ 1, 2, 3, 4 } };

  // Expected to pass.
  p0: assert final ($bits(s) == 4 * 32 + 4 * 32);
  p11: assert property (s.array1[0] == 1);
  p12: assert property (s.array1[1] == 2);
  p13: assert property (s.array1[2] == 3);
  p14: assert property (s.array1[3] == 4);
  p21: assert property (s.array2[0] == 1);
  p22: assert property (s.array2[1] == 2);
  p23: assert property (s.array2[2] == 3);
  p24: assert property (s.array2[3] == 4);

endmodule
