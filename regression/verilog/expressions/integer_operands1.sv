// Operands of type integer take part in the determination of the type
// of an operation as the 32-bit signed vector type (1800-2017 6.11,
// 11.8.2), both in constant expressions and in the design. This applies
// to two integer operands, e.g., two $clog2 results, and to an integer
// operand together with a vector operand.
module main #(parameter PORTS = 16, parameter PORTS_IN = 16,
              localparam PORT_SEL_BITS = $clog2(PORTS) - $clog2(PORTS_IN),
              localparam W = 8 + PORT_SEL_BITS)
  (input clk, input [W-1:0] d, input [7:0] b);

  localparam A = $clog2(16) + $clog2(8);

  integer c = $clog2(16) * $clog2(4);

  p0: assert property (@(posedge clk) $bits(d) == 8);
  p1: assert property (@(posedge clk) A == 7);
  p2: assert property (@(posedge clk) c == 8);

  // the result type of two integer operands
  p3: assert property (@(posedge clk) $bits($clog2(16) + $clog2(8)) == 32);

  // the result type of an integer and an 8-bit operand is 32 bits, not 8
  p4: assert property (@(posedge clk) $bits($clog2(16) + b) == 32);
  p5: assert property (@(posedge clk) $clog2(16) + b == b + 32'd4);

endmodule
