module main(input clk);
  reg [3:0] r;
  always @(posedge clk) r <= 4'b1010;
  // $isunknown applied to a non-constant signal. This must be synthesized,
  // not treated as a constant expression.
  p0: assert property (@(posedge clk) $isunknown(r) == 1'b0);
endmodule
