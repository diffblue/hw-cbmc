module main(input clk, input en, input sel, input d,
  output reg q1, q2, q4, q5, q6, r);

  // different ways of gating a clock
  wire gclk1 = ~(~clk | ~en);
  wire gclk2 = sel ? clk : 1'b0;
  wire gclk4 = clk && en && sel;
  wire gclk5 = gclk4 ^ 1'b1;
  wire gclk6 = sel ? clk : en ? clk : 1'b1;

  always @(posedge gclk1) q1 <= d;
  always @(negedge gclk2) q2 <= d;
  always @(posedge gclk4) q4 <= d;
  always @(negedge gclk5) q5 <= d;
  always @(posedge gclk6) q6 <= d;

  // the base clock
  always @(posedge clk) r <= d;
endmodule
