module main(input clk, input en, input d, output reg q, output reg r);
  wire gclk = clk & en;

  // q is on the gated clock, r is on the base clock
  always @(posedge gclk) q <= d;
  always @(posedge clk) r <= d;

  // q cannot change while en is low
  p_hold: assert property (!en |=> $stable(q));

  // q follows d while en is high
  p_follow: assert property (en |=> q == $past(d));

  // r is not gated
  p_r: assert property (##1 r == $past(d));
endmodule
