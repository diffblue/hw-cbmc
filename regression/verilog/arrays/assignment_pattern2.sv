module main;

  reg [7:0] my_array[10] = '{1, 2, 3, 4, 5, 6, 7, 8, 9, 10};

  p0: assert final (my_array[0] == 1);
  p1: assert final (my_array[9] == 10);

endmodule
