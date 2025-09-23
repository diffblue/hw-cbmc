module main(input[31:0] in1, in2, in3);

  // follows
  // http://www.asic-world.com/verilog/operators2.html

  // logical shift
  always assert shift_p1:  4'b1001 << 1 === 4'b0010;
  always assert shift_p2:  4'b10x1 << 1 === 4'b0x10;
  always assert shift_p3:  4'b10z1 << 1 === 4'b0z10;
  always assert shift_p4:  4'b1001 >> 1 === 4'b0100;
  always assert shift_p5:  4'b10x1 >> 1 === 4'b010x;
  always assert shift_p6:  4'b10z1 >> 1 === 4'b010z;
  always assert shift_p7:  4'b1111 << 1 === 5'b11110;
  always assert shift_p8:  1 << 6 === 64;

  // arithmetic shift
  always assert shift_p9:  -1 >>> 1 === -1;
  always assert shift_p10:   1 >>> 1 === 0;
  always assert shift_p11: -2 >>> 1 === -1;

endmodule
