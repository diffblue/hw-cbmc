module main(input clk);

  // an 8-bit counter, giving a recurrence diameter of 2^8-1 = 255
  reg [7:0] cnt;
  initial cnt = 0;
  always @(posedge clk) cnt = cnt + 1;

  // p0 is an "always" property; its completeness threshold is the
  // recurrence diameter of the design. This is larger than the completeness
  // threshold of p1 below.
  p0: assert property (@(posedge clk) cnt <= 255);

  // p1 is a pure state predicate (immediate assertion in the initial
  // state), whose completeness threshold is 0. It must be proved unbounded
  // (CT=0) even though another property with a larger completeness
  // threshold is present. Previously the engine compared p1's own threshold
  // against the maximum threshold over all properties and gave up on p1.
  initial p1: assert property (cnt == 0);

endmodule
