module main(input[31:0] in1, in2, in3);

  // follows
  // http://www.asic-world.com/verilog/operators1.html

  // equality
  always assert equal_p1:  (4'bx001 ===  4'bx001) == 1;
  always assert equal_p2:  (4'bx0x1 ===  4'bx001) == 0;
  always assert equal_p3:  (4'bz0x1 ===  4'bz0x1) == 1;
  always assert equal_p4:  (4'bz0x1 ===  4'bz001) == 0;
  always assert equal_p5:  (4'bx0x1 !==  4'bx001) == 1;
  always assert equal_p6:  (4'bz0x1 !==  4'bz001) == 1;
  always assert equal_p7:  (5       ==   10     ) == 0;
  always assert equal_p8:  (5       ==    5     ) == 1;
  always assert equal_p9:  (5       !=    5     ) == 0;
  always assert equal_p10: (5       !=    6     ) == 1;    

endmodule
