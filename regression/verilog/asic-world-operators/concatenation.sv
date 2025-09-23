module main(input[31:0] in1, in2, in3);

  // follows
  // http://www.asic-world.com/verilog/operators2.html

  // concatenation
  always assert concat_p1: {4'b1001,4'b10x1} === 'b100110x1;

endmodule
