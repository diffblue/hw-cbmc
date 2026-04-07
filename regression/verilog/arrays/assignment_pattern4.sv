module main;

  int my_array[10] = '{ 1: 1, 2: 2, 3: 0, default: 10 };

  p0: assert final (my_array[0] == 10);
  p1: assert final (my_array[1] == 1);
  p2: assert final (my_array[2] == 2);
  p3: assert final (my_array[3] == 0);
  p4: assert final (my_array[4] == 10);
  p5: assert final (my_array[5] == 10);
  p6: assert final (my_array[6] == 10);
  p7: assert final (my_array[7] == 10);
  p8: assert final (my_array[8] == 10);
  p9: assert final (my_array[9] == 10);

endmodule
