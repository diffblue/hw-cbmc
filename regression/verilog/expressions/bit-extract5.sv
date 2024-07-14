module main;

  wire [31:0] w1 = 'b1;
  wire [32:1] w2 = 'b1;
  wire [0:31] w3 = 'b1;
  wire [1:32] w4 = 'b1;

  p0: assert final (w1[0] && !w1[31]);
  p1: assert final (w2[1] && !w2[32]);
  p2: assert final (w3[31] && !w3[0]);
  p3: assert final (w4[32] && !w4[1]);

endmodule
