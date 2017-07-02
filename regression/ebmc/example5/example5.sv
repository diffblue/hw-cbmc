module top(input clk);

  reg [31:0] x, y;

  initial x=0;
  initial y=0;

  always @(posedge clk) x<=x+1;
  always @(posedge clk) y<=y+2;

  p1: assert property (x==0 |-> ##[1:$] y==18);

endmodule
