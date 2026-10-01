// The elements of an unpacked array of a packed struct are assigned
// separately. The value of the array is composed from the elements.
typedef struct packed { logic [10:0] a; logic [10:0] b; } t_s;

module main(input clk);
  t_s y [0:1];
  assign y[0] = '0;
  assign y[1] = {11'd3, 11'h7FF};

  p0: assert property (@(posedge clk) y[0] == 0);
  p1: assert property (@(posedge clk) y[1].a == 11'd3);
  p2: assert property (@(posedge clk) y[1].b == 11'h7FF);
  p3: assert property (@(posedge clk) y[1] == {11'd3, 11'h7FF});
endmodule
