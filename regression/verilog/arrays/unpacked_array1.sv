module main;

  int my_array0[10];
  int my_array1[9:0];
  int my_array2[4:-5];
  int my_array3[0:9];
  int my_array4[-10:-1];

  initial begin
    p0a: assert($left(my_array0) == 0   && $right(my_array0) == 9);
    p1a: assert($left(my_array1) == 9   && $right(my_array1) == 0);
    p2a: assert($left(my_array2) == 4   && $right(my_array2) == -5);
    p3a: assert($left(my_array3) == 0   && $right(my_array3) == 9);
    p4a: assert($left(my_array4) == -10 && $right(my_array4) == -1);

    p0b: assert($increment(my_array0) == -1);
    p1b: assert($increment(my_array1) == 1);
    p2b: assert($increment(my_array2) == 1);
    p3b: assert($increment(my_array3) == -1);
    p4b: assert($increment(my_array4) == -1);
  end

endmodule
