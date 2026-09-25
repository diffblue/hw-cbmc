module main(input clk);

  reg [3:0] c = 0;

  always @(posedge clk)
    c <= c + 1;

  // c==3 holds at t=3, within the window [2:3] from t=0.
  // Any evaluation attempt that has not completed within the bound
  // is inconclusive, and must not yield a counterexample.
  // Expected to pass up to the bound.
  p0: assert property (@(posedge clk) s_eventually[3:3] c == 3);
  p1: assert property (@(posedge clk) s_eventually[2:3] c == 3);

  // s_nexttime[3] is equivalent to s_eventually[3:3], and is handled
  // correctly.
  p2: assert property (@(posedge clk) s_nexttime[3] c == 3);

endmodule
