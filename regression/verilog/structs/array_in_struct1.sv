module main;

  struct {
    // unpacked
    int array1[4];

    // packed
    bit [3:0] [31:0] array2;
  } s;

  initial begin
    s = '{ '{ 1, 2, 3, 4 }, '{ 1, 2, 3, 4 } };

    // Expected to pass.
    p0: assert($bits(s) == 4 * 32 + 4 * 32);
    p11: assert(s.array1[0] == 1);
    p12: assert(s.array1[1] == 2);
    p13: assert(s.array1[2] == 3);
    p14: assert(s.array1[3] == 4);
    p21: assert(s.array2[0] == 4);
    p22: assert(s.array2[1] == 3);
    p23: assert(s.array2[2] == 2);
    p24: assert(s.array2[3] == 1);
  end

endmodule
