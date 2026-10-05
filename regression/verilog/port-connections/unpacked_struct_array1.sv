// An unpacked array of a packed struct is connected to ports declared
// as an unpacked array of a packed vector of the same width. The
// element types are equivalent (1800-2017 6.22.2), and hence the
// unpacked arrays are assignment compatible (7.6).
typedef struct packed { logic [10:0] a; logic [10:0] b; } t_s;

module child(input clk,
             output logic [21:0] o [0:1],
             input logic [21:0] i [0:1]);
  always_ff @(posedge clk) begin
    o[0] <= 22'h2A;
    o[1] <= {11'd3, 11'd5};
  end
  p_in: assert property (@(posedge clk) i[1] == 22'h7FF);
endmodule

module main(input clk);
  t_s x [0:1];
  t_s y [0:1];
  assign y[0] = '0;
  assign y[1] = {11'd0, 11'h7FF};

  // output port: array of vectors drives an array of structs;
  // input port: array of structs drives an array of vectors
  child c(.clk(clk), .o(x), .i(y));

  p0: assert property (@(posedge clk) ##1 x[0].b == 11'h2A && x[0].a == 0);
  p1: assert property (@(posedge clk) ##1 x[1].a == 11'd3 && x[1].b == 11'd5);

  // a row of a two-dimensional array
  t_s m [0:1][0:1];
  child c2(.clk(clk), .o(m[0]), .i(y));
  p2: assert property (@(posedge clk) ##1 m[0][1].b == 11'd5);

  // an assignment between the two array types
  logic [21:0] z [0:1];
  assign z = y;
  p3: assert property (@(posedge clk) z[1] == 22'h7FF);

endmodule
