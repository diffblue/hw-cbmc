// Compound assignment with operands of differing widths (division).
//
// Per IEEE 1800-2017 11.4.1, "a /= b" is equivalent to "a = a / (b)".
// By the expression-sizing rules of 11.6.1/11.8.2 the division is a
// self-determined-free (context-determined) operation whose operands are
// sized to the maximum of the operands and the assignment target. Here a is
// 8-bit and b is 16-bit, so the division must be performed at 16 bits:
// 200 / 300 == 0, and a must become 0.
//
// EBMC instead truncates b to the 8-bit type of a before the operation
// (200 / (300 % 256 = 44) = 4), so the property is wrongly REFUTED.
module main(input clk);
  reg [7:0] a = 200;
  reg [15:0] b = 300;
  always @(posedge clk) a /= b; // a = a / b, 16-bit: 200 / 300 == 0
  p0: assert property (@(posedge clk) ##1 a == 0);
endmodule
