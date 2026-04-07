module main;

  bit [0:4][31:0] my_array1;
  bit [4:0][31:0] my_array2;

  initial begin
    my_array1 = '{ 1, 2, 3, 4, 5 };
    my_array2 = '{ 1, 2, 3, 4, 5 };
    p1: assert(my_array1[0] == 1);
    p2: assert(my_array2[0] == 5);
  end

endmodule
