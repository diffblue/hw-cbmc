// x and z assigned to one-bit variables in procedural blocks, e.g., in
// the default of a case statement. The RTL construction failed a
// precondition in from_integer when it simplified the conversion of the
// four-valued constant to bool.
module main(input clk, input a, input b);
  reg q = 0;
  reg n, m, z;

  always @(*)
    case(q)
      1'b0: n = a;
      1'b1: n = b;
      default: n = 1'bx;
    endcase

  always @(*) m = 1'bx;
  always @(*) z = 1'bz;

  always @(posedge clk) q <= n;

  // Variables are two-valued; x and z are converted as for wider
  // variables, e.g., reg [3:0] v = 4'bx.
  p0: assert property (@(posedge clk) m == 0 && z == 0);
  p1: assert property (@(posedge clk) q == 0 -> n == a);
endmodule
