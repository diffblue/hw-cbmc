// An output port of an unpacked array type is connected to an unpacked
// array with a different element width, which is an error.
typedef struct packed { logic [10:0] a; logic [9:0] b; } t_21;

module child(input clk, output logic [21:0] o [0:0]);
endmodule

module main(input clk);
  t_21 x [0:0];
  child c(.clk(clk), .o(x));
endmodule
