module main;

  reg [31:0] x;
  wire clk;

  initial x=0;

  always @(posedge clk)
    if(x != 5)
      x<=x+1;

  // fails once we see the lasso 0, 1, 2, 3, 4, 5, 5
  initial p0: assert property (##[0:$] x==10);

endmodule
