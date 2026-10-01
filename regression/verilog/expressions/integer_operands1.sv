// Operations on two operands of type integer, e.g., two $clog2 results,
// have the 32-bit signed vector type (1800-2017 6.11), both in constant
// expressions and in the design.
module main #(parameter PORTS = 16, parameter PORTS_IN = 16,
              localparam PORT_SEL_BITS = $clog2(PORTS) - $clog2(PORTS_IN),
              localparam W = 8 + PORT_SEL_BITS)
  (input clk, input [W-1:0] d);

  localparam A = $clog2(16) + $clog2(8);

  integer a, b;
  wire [31:0] w = a - b;
  integer c = $clog2(16) * $clog2(4);

  p0: assert property (@(posedge clk) $bits(d) == 8);
  p1: assert property (@(posedge clk) A == 7);
  p2: assert property (@(posedge clk) w == a - b);
  p3: assert property (@(posedge clk) c == 8);

endmodule
