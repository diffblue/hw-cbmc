module main(input clk);

  // three-state cycle 0 -> 1 -> 2 -> 0 -> ...
  reg [1:0] s = 0;

  always @(posedge clk)
    s <= (s == 2) ? 0 : s + 1;

  // When s==1, then s==1 holds until s==2 in the next cycle.
  // Expected to pass.
  p0: assert property (@(posedge clk) s == 1 |-> (s == 1) s_until (s == 2));

endmodule
