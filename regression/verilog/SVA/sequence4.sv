module main;

  reg [31:0] x;
  wire clk;

  initial x=0;

  always @(posedge clk)
    x<=x+1;

  // sequence concatenation
  initial p0: assert property (x == 0 ##1 x == 1 ##1 x == 2);

  initial p1: assert property (x == 0 ##0 x == 0 ##1 x == 1);

endmodule
