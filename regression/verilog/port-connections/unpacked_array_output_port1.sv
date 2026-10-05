// An output port of an unpacked array type drives an unpacked array
// with a different range, a different direction, and an element type
// that is converted (1800-2017 7.6). The elements correspond in
// left-to-right order.
module child(input clk, output int o [0:2]);
  always_ff @(posedge clk) begin
    o[0] <= 100;
    o[1] <= 200;
    o[2] <= 300;
  end
endmodule

module main(input clk);
  // same element type, descending range
  int x [3:1];
  child c1(.clk(clk), .o(x));
  p0: assert property (@(posedge clk) ##1 x[3] == 100 && x[2] == 200 && x[1] == 300);

  // element type converted (truncated), ascending range with offset
  byte y [5:7];
  child c2(.clk(clk), .o(y));
  p1: assert property (@(posedge clk) ##1 y[5] == 100 && y[6] == 8'(200) && y[7] == 8'(300));
endmodule
