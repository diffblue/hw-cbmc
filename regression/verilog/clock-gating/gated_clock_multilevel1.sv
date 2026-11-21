module main(input clk, input en1, en2, input d, output reg q, output reg r);
  wire gclk1 = clk & en1;
  wire gclk2 = gclk1 & en2;

  // gated clocks may be gated again
  always @(posedge gclk1) r <= d;
  always @(posedge gclk2) q <= d;

  // the base clock
  always @(posedge clk) ;
endmodule
