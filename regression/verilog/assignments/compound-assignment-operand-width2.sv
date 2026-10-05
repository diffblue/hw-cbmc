// Compound assignment with a wide shift amount (right shift).
//
// Per IEEE 1800-2017 11.4.1, "a >>= b" is equivalent to "a = a >> (b)".
// The right operand of a shift is self-determined (11.6.1/11.8.2), so the
// shift amount b must keep its own 16-bit width and must NOT be truncated to
// the width of a. Here a is 8-bit and b == 256, so a >> 256 == 0 and a must
// become 0.
//
// EBMC instead truncates b to the 8-bit type of a before the operation
// (256 % 256 == 0, i.e. a shift by 0), so a stays 0xff and the property is
// wrongly REFUTED.
module main(input clk);
  reg [7:0] a = 8'hff;
  reg [15:0] b = 16'd256;
  always @(posedge clk) a >>= b; // a = a >> b, self-determined amount 256
  p0: assert property (@(posedge clk) ##1 a == 0);
endmodule
