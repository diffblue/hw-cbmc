module main(input clk);

  // values of real variables in traces
  real r = 1.5;
  shortreal s = 0.25;

  always @(posedge clk)
    r = 2.5;

  p0: assert property (r == 1.5);

endmodule
