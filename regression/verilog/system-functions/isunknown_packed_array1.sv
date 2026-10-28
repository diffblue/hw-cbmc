// $isunknown applied to a packed array with a z (IEEE 1800-2017 20.9).
module main(input clk);
  logic [1:0][3:0] pa = {4'b0000, 4'b00z0};

  always @(posedge clk) pa <= pa;

  p0: assert property (@(posedge clk) $isunknown(pa) == 1);
  p1: assert property (@(posedge clk) $isunknown(pa[1]) == 0);
  p2: assert property (@(posedge clk) $isunknown(pa[0]) == 1);
endmodule
