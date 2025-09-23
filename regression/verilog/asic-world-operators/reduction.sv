module main(input[31:0] in1, in2, in3);

  // follows
  // http://www.asic-world.com/verilog/operators2.html

  // reduction
  always assert redu_p1:   & 4'b1001 === 'b0;
  always assert redu_p2:   & 4'bx111 === 'bx;
  always assert redu_p3:   & 4'bz111 === 'bx;
  always assert redu_p4:  ~& 4'b1001 === 'b1;
  always assert redu_p5:  ~& 4'bx001 === 'b1;
  always assert redu_p6:  ~& 4'bz001 === 'b1;
  always assert redu_p7:   | 4'b1001 === 'b1;
  always assert redu_p8:   | 4'bx000 === 'bx;
  always assert redu_p9:   | 4'bz000 === 'bx;
  always assert redu_p10: ~| 4'b1001 === 'b0;
  always assert redu_p11: ~| 4'bx001 === 'b0;
  always assert redu_p12: ~| 4'bz001 === 'b0;
  always assert redu_p13:  ^ 4'b1001 === 'b0;
  always assert redu_p14:  ^ 4'bx001 === 'bx;
  always assert redu_p15:  ^ 4'bz001 === 'bx;
  always assert redu_p16: ~^ 4'b1001 === 'b1;
  always assert redu_p17: ~^ 4'bx001 === 'bx;
  always assert redu_p18: ~^ 4'bz001 === 'bx;

endmodule
