module main(input clk, input [7:0] in);

  reg [7:0] x;
  initial x = 0;

  always @(posedge clk)
    x = in;

  // The input can only become 5 if it was 4 before.
  // The weak semantics at the end of the bound must not
  // constrain later bounds.
  a0: assume property (always (in == 5 implies in == 5 && $past(in) == 4));
  a1: assume property (always (in == 4 implies s_nexttime in == 5));

  // fails with 3 states: in=4, in=5
  p0: assert property (x != 5);

endmodule
