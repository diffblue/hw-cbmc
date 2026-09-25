module main(input clk, input rst, input a, input b);

  // rst is asserted in the cycle after a
  assume property (@(posedge clk) a |=> rst);

  // 1800-2017 16.12: if the disable condition becomes true at any point
  // between the start of the evaluation attempt and its end, the attempt
  // is disabled and evaluates to true.  Here, rst is true in the cycle in
  // which b would be checked, and hence every attempt is disabled.
  // Expected to pass.
  p0: assert property (@(posedge clk) disable iff (rst) a |=> b);

endmodule
