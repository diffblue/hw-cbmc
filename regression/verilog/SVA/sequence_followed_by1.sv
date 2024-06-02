module main(input clk);

  reg [31:0] x = 0;

  always @(posedge clk)
    x<=x+1;

  initial p0: assert property (x == 0 #=# x == 1 #=# x == 2);

  initial p1: assert property (x == 0 #-# ##1 x == 1 #-# ##1 x == 2);

endmodule
