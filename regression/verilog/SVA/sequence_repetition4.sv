module main(input clk);

  reg [31:0] x = 0;

  // 0 1 0 1 0 1 ...
  always_ff @(posedge clk)
    x = x == 0 ? 1 : 0;

  // should pass
  initial p0: assert property ((x == 0 ##1 x == 1)[*2]);

  // should fail
  initial p1: assert property ((x == 0 ##1 x == 1 ##1 x == 0)[*2]);

endmodule
