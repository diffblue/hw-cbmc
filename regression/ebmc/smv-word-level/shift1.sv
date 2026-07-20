module main;

  wire [7:0] a = 8'hA5;
  wire [7:0] shl = a << 2;
  wire [7:0] lshr = a >> 2;
  wire signed [7:0] sa = -8'sd10;
  wire signed [7:0] ashr = sa >>> 2;

endmodule
