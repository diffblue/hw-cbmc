module main(input clk);

  reg [7:0] d;

  initial d = 0;

  // the state repeats after 256 steps
  always @(posedge clk) d <= d + 1;

  p0: assert property (always s_eventually d == 3);
  p1: assert property (always (d == 2 implies s_eventually d == 5));
  p2: assert property (always (d == 1 |-> (d < 9 s_until d == 9)));
  p3: assert property (s_eventually always d != 3);

endmodule
