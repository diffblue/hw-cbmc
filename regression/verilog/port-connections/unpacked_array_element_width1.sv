// Unpacked arrays whose element types differ in width are assignment
// compatible (1800-2017 7.6); the elements are converted as in an
// assignment, i.e., truncated or extended. This applies to assignments
// and to input and output port connections.
typedef struct packed { logic [10:0] a; logic [9:0] b; } t_21;

module child(input clk,
             output logic [21:0] o [0:0],
             input logic [21:0] i [0:0]);
  always_ff @(posedge clk) o[0] <= 22'h3FFFFF;
  p_in: assert property (@(posedge clk) i[0] == 22'h0003FF);
endmodule

module main(input clk);
  t_21 x [0:0];
  t_21 y [0:0];
  assign y[0] = {11'd0, 10'h3FF};

  child c(.clk(clk), .o(x), .i(y));

  // output port: the 22-bit element is truncated to the 21-bit struct
  p0: assert property (@(posedge clk) ##1 x[0] == 21'h1FFFFF);

  // assignment: the 21-bit struct is zero-extended to 22 bits
  logic [21:0] z [0:0];
  assign z = y;
  p1: assert property (@(posedge clk) z[0] == 22'h0003FF);
endmodule
