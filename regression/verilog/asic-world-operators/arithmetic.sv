module main(input[31:0] in1, in2, in3);

  // follows
  // http://www.asic-world.com/verilog/operators1.html

  // arithmetic
  always assert arith_p1:  5  +  10 ===  15;
  always assert arith_p2:  5  -  10 ===  -5;
  always assert arith_p3:  10 -   5 ===   5;
  always assert arith_p4:  10 *   5 ===  50;
  always assert arith_p5:  10 /   5 ===   2;
  always assert arith_p6:  10 /  -5 ===  -2;
  always assert arith_p7:  10 %   3 ===   1;
  always assert arith_p8:  +5       ===   5;
  always assert arith_p9:  -5       ===  -5;
  always assert arith_p10:  2**3    ===   8;
  always assert arith_p11: -2**3    ===  -8;

endmodule
