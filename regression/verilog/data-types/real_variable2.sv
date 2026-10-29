module main(input clk, input c);

  // a conditional assignment to a real variable, with arithmetic
  real r = 1.5;

  always @(posedge clk)
    if(c) r = r + 1.0;

  p0: assert property (r >= 1.5);
  p1: assert property (r < 3.0);

endmodule
