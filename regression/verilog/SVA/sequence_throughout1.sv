module main(input clk);

  reg [31:0] x = 0;

  always @(posedge clk)
    x<=x+1;

  // should pass
  initial p0: assert property (x >= 0 throughout x==0 ##1 x==1 ##1 x==2);

  // should fail owing to LHS
  initial p1: assert property (x <= 1 throughout x==0 ##1 x==1 ##1 x==2);

  // should fail owing to RHS
  initial p2: assert property (1 throughout x==0 ##1 x==1 ##1 x==3);

endmodule
