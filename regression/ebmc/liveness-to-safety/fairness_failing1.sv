module main(input clk, input act);

  reg x;

  initial x=0;

  always @(posedge clk)
    x <= x;

  // Two fairness assumptions that cannot be observed
  // in the same cycle.
  assume property (always s_eventually act);
  assume property (always s_eventually !act);

  // expected to fail: x is stuck at 0
  p0: assert property (s_eventually x);

endmodule
