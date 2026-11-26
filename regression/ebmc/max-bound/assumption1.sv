module main(input clk, input [7:0] in);

  reg [7:0] x;
  initial x = 0;

  always @(posedge clk)
    x = x + in;

  // the increment is at most 1
  a0: assume property (in <= 1);

  // fails at depth 5 given the assumption
  p0: assert property (x != 5);

  // fails at depth 11 given the assumption
  p1: assert property (x <= 10);

endmodule
