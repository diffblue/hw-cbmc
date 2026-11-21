module gated(input clk, input en, input d, output reg q);
  wire gclk = clk & en;
  always @(posedge gclk) q <= d;
  // q cannot change while en is low.
  p_hold: assert property (@(posedge clk) !en |=> $stable(q));
endmodule
