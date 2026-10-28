// Nets defined by nested concatenations, as a whole and by slices.
module main(input clk, input [1:0] x);
  wire [5:0] v, w;
  assign v = {{x, 2'b10}, 2'b01};
  assign w[1:0] = 2'b01;
  assign w[5:2] = {{x}, {2'b10}};
  p0: assert property (@(posedge clk) v == {x, 2'b10, 2'b01});
  p1: assert property (@(posedge clk) w == {x, 2'b10, 2'b01});
  p2: assert property (@(posedge clk) v[5:4] == 2'b00); // fails
endmodule
