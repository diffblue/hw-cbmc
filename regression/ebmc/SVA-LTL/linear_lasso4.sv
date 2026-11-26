module main(input clk, input i);

  reg r;

  initial r = 0;

  always @(posedge clk) r <= i;

  // i is false from the third state on
  a0: assume property (nexttime [2] !i);

  // holds, given the assumption
  initial p0: assert property (s_eventually always !r);

endmodule
