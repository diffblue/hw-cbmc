module main(input clk, input [3:0] x);

  reg [3:0] r;
  initial r = 0;
  always @(posedge clk) r <= x;

  // Every state has a successor that satisfies the assumption.
  a0: assume property (@(posedge clk) x < 8);

  p0: assert property (@(posedge clk) r < 8);

endmodule
