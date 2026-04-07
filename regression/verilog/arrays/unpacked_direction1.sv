module main;

  int my_array0[5];
  int my_array1[0:4]; // same as [5]
  int my_array2[4:0];

  initial begin : blk
    my_array0 = '{ 1, 2, 3, 4, 5 };
    my_array1 = '{ 1, 2, 3, 4, 5 };
    my_array2 = '{ 1, 2, 3, 4, 5 };
    p0: assert(my_array0[0] == 1);
    p1: assert(my_array1[0] == 1);
    p2: assert(my_array2[0] == 5);
  end

endmodule
