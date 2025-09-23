module main(input[31:0] in1, in2, in3);

  // follows
  // http://www.asic-world.com/verilog/operators1.html

  // bit-wise
  always assert bit_p1:  ~4'b0001             === 4'b1110;
  always assert bit_p2:  ~4'bx001             === 4'bx110;
  always assert bit_p3:  ~4'bz001             === 4'bx110;
  always assert bit_p4:  (4'b0001 &  4'b1001) === 4'b0001;
  always assert bit_p5:  (4'b1001 &  4'bx001) === 4'bx001;
  always assert bit_p6:  (4'b1001 &  4'bz001) === 4'bx001;
  always assert bit_p7:  (4'b0001 |  4'b1001) === 4'b1001;
  always assert bit_p8:  (4'b0001 |  4'bx001) === 4'bx001;
  always assert bit_p9:  (4'b0001 |  4'bz001) === 4'bx001;
  always assert bit_p10: (4'b0001 ^  4'b1001) === 4'b1000;
  always assert bit_p11: (4'b0001 ^  4'bx001) === 4'bx000;
  always assert bit_p12: (4'b0001 ^  4'bz001) === 4'bx000;
  always assert bit_p13: (4'b0001 ~^ 4'b1001) === 4'b0111;
  always assert bit_p14: (4'b0001 ~^ 4'bx001) === 4'bx111;
  always assert bit_p15: (4'b0001 ~^ 4'bz001) === 4'bx111;

endmodule
