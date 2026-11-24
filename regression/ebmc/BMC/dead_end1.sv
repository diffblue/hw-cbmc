module main(input clk);

  reg [3:0] cnt;
  initial cnt = 0;
  always @(posedge clk) cnt <= cnt + 1;

  // No path satisfies the assumption beyond the state with cnt == 4.
  a0: assume property (@(posedge clk) cnt != 5);

  // fails in the state with cnt == 3
  p0: assert property (@(posedge clk) cnt != 3);

endmodule
