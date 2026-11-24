module main(input clk);

  reg [3:0] x;
  initial x = 0;
  always @(posedge clk) x <= x + 1;

  // all violated in the state with x == 3
  initial p0: assert property (x <= 2 until x == 4);
  initial p1: assert property (x <= 2 s_until x == 4);
  initial p2: assert property (x <= 2 until_with x == 4);
  initial p3: assert property (x <= 2 s_until_with x == 4);

endmodule
