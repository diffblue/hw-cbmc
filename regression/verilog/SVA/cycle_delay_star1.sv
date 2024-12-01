module main;

  reg [31:0] x;
  wire clk;

  initial x=0;

  always @(posedge clk)
    if(x < 5)
      x<=x+1;

  // Same as ##[0:$] x==2 ##1 x==3
  initial p0: assert property (##[*] x==2 ##1 x==3);

endmodule
