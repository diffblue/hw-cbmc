module main(input[31:0] in1, in2, in3);

  // follows
  // http://www.asic-world.com/verilog/operators1.html

  // logical
  always assert logic_p1:  (1'b1 && 1'b1) === 'b1;
  always assert logic_p2:  (1'b1 && 1'b0) === 'b0;
  always assert logic_p3:  (1'b1 && 1'bx) === 'bx;
  always assert logic_p4:  (1'b1 || 1'b0) === 'b1;
  always assert logic_p5:  (1'b0 || 1'b0) === 'b0;
  always assert logic_p6:  (1'b0 || 1'bx) === 'bx;
  always assert logic_p7:  (! 1'b1      ) === 'b0;
  always assert logic_p8:  (! 1'b0      ) === 'b1;
  always assert logic_p9:  (!2'b10      ) === 'b0;
  always assert logic_p10: (! 1'bx      ) === 'bx;
  always assert logic_p11: (! 1'bz      ) === 'bx;

endmodule
