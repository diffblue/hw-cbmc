// $isunknown applied to nets that carry x or z (IEEE 1800-2017 6.5, 6.6.1,
// 20.9).
module main(input clk);
  wire [3:0] w1 = 4'b1x00;     // net declaration assignment
  wire [3:0] w2;               // no driver: z
  logic en = 0;
  wire [3:0] w3;
  assign w3 = en ? 4'b0101 : 4'bz;

  always @(posedge clk) en <= en;

  p0: assert property (@(posedge clk) $isunknown(w1) == 1);
  p1: assert property (@(posedge clk) $isunknown(w2) == 1 && w2 === 4'bzzzz);
  p2: assert property (@(posedge clk) $isunknown(w3) == 1 && w3 === 4'bzzzz);
endmodule
