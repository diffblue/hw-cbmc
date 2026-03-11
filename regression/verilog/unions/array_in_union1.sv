module main;

  union packed {
    bit [3:0] [0:0] array;
    bit [3:0] as_vector;
  } u;

  initial begin
    u.array = '{ 1, 1, 0, 1 };

    // Expected to pass.
    p0: assert($bits(u) == 4);
    p11: assert(u.array[0] == 1);
    p12: assert(u.array[1] == 0);
    p13: assert(u.array[2] == 1);
    p14: assert(u.array[3] == 1);
    p21: assert(u.as_vector == 4'b1101);
  end

endmodule
