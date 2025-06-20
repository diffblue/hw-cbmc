module main(input clk);

  reg [7:0] x = 0;

  always @(posedge clk)
    x<=x+1;

  // The empty sequence does not match
  initial p0: assert property (1[*0]);

  // But can be concatenated -- expected to pass
  initial p1: assert property (1[*0] ##1 x == 0);
  initial p2: assert property (x == 0 ##1 1[*0]);

  // But can be concatenated -- expected to fail
  initial p3: assert property (1[*0] ##0 1);
  initial p4: assert property (1 ##0 1[*0]);

endmodule
