module main(input clk);

  // An increasing range: v[0] is the most significant bit.
  reg [0:7] v;

  initial v = 0;

  always @(posedge clk)
    v[0] = 1;

  p0: assert property (@(posedge clk) ##1 v[0] == 1);
  p1: assert property (@(posedge clk) ##1 v == 8'h80);

endmodule
