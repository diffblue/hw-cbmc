// 1800-2017 23.3.3.5

module sub(input i);
endmodule

module main;

  sub my_instance[8:1](8'b1111_0000);

  initial #1 assert(my_instance[1].i == 0);
  initial #1 assert(my_instance[2].i == 0);
  initial #1 assert(my_instance[3].i == 0);
  initial #1 assert(my_instance[4].i == 0);
  initial #1 assert(my_instance[5].i == 1);
  initial #1 assert(my_instance[6].i == 1);
  initial #1 assert(my_instance[7].i == 1);
  initial #1 assert(my_instance[8].i == 1);

endmodule
