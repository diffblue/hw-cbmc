module main(input clk);

  // variables of the real types in properties
  real r = 1.5;
  shortreal s = 0.25;

  always @(posedge clk)
    r = 2.5;

  p0: assert property (r == 1.5 || r == 2.5);
  p1: assert property (r >= 1.5);
  p2: assert property (s == 0.25);

endmodule
