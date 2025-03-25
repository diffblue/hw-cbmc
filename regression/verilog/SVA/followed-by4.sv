module main(input clk);

  reg [31:0] x;

  initial x=0;

  // 0, 1, ...
  always @(posedge clk)
    x<=x+1;

  // fails in the 2nd timeframe since the LHS doesn't match
  p1: assert property (x==0 #-# 1);

  // the RHS only needs to hold from _any one_ of the LHS matches,
  // not all
  initial p2: assert property ((1 or ##2 1) #-# x==2);
  initial p3: assert property ((1 or ##2 1) #-# x==0);

endmodule
