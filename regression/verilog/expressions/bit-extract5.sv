module main;

  wire [31:0] w1 = 'b1;
  wire [32:1] w2 = 'b1;
  wire [0:31] w3 = 'b1;
  wire [1:32] w4 = 'b1;

  p0: assert property (w1[0] and !w1[31]);
  p1: assert property (w2[1] and !w2[32]);
  p2: assert property (w3[31] and !w3[0]);
  p3: assert property (w4[32] and !w4[1]);

endmodule
