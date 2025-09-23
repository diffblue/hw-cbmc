module main(input[31:0] in1, in2, in3);

  // follows
  // http://www.asic-world.com/verilog/operators2.html

  // conditional
  always assert cond_p1: (1'b0 ? 2'b11 : 1'b0) === 2'b00;
  always assert cond_p2: (1'b1 ? 2'b11 : 1'b0) === 2'b11;
  always assert cond_p3: (1'bz ? 2'b11 : 1'b0) === 2'bxx;
  always assert cond_p4: (1'bx ? 2'b11 : 1'b0) === 2'bxx;
  always assert cond_p5: (1'b1 ? 2'b11 : 1'bz) === 2'b11;
  always assert cond_p6: (1'b1 ? 2'b11 : 1'bx) === 2'b11;
  always assert cond_p7: (1'b0 ? 2'b11 : 1'bz) === 2'b0z;
  always assert cond_p8: (1'b0 ? 2'b11 : 1'bx) === 2'b0x;

endmodule
