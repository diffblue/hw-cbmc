module main(input clk);

  reg [7:0] x = 0;

  always @(posedge clk)
    x<=x+1;

  // The empty sequence does not match
  initial p0: assert property (1[*0]);

  // But can be concatenated
  initial p1: assert property (1[*0] ##1 x == 0);

endmodule
