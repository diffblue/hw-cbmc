module main(input clk);

  reg [3:0] c = 0;

  always @(posedge clk)
    c <= c + 1;

  // fails at t=3, as c==5 at t=5
  p0: assert property (@(posedge clk) always[0:2] c != 5);

  // fails at t=3, as c==5 at t=5
  p1: assert property (@(posedge clk) always[1:2] c != 5);

  // fails at t=0, as c==5 at t=5
  p2: assert property (@(posedge clk) always[1:$] c != 5);

  // fails at t=2, as c==4 at t=4
  p3: assert property (@(posedge clk) c == 2 |-> always[0:2] c != 4);

endmodule
