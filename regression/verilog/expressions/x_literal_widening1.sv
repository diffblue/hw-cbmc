module main(input clk, input [7:0] in);

  reg [31:0] r;

  initial r = 0;

  // A 1-bit x literal is assigned to a 32-bit register.
  // 1800-2017 11.8.3: the rhs is extended to the width of the lhs.
  always @(posedge clk)
    if(in == 0)
      r <= 1'bx;
    else
      r <= in;

  p0: assert property (in == 0 || r == r);

endmodule
