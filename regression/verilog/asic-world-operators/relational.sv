module main(input[31:0] in1, in2, in3);

  // follows
  // http://www.asic-world.com/verilog/operators1.html

  // relational
  always assert rel_p1: (5    <= 10) === 1;
  always assert rel_p2: (5    >= 10) === 0;
  always assert rel_p3: (1'bx <= 10) === 1'bx;
  always assert rel_p4: (1'bz <= 10) === 1'bx;
  always assert rel_p5: (-10  <= 10) === 1;

endmodule
