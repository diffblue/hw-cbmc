module main(input clk, input a, input b);

  reg r = 0;

  always @(posedge clk)
    r <= a;

  // an assumption with a temporal operator
  assume property (a |=> b);

  // holds given the assumption, as r is the value of a in the previous cycle
  p0: assert property (r -> b);

endmodule
