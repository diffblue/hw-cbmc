// Indexed part-selects of packed arrays select ELEMENTS
// (1800-2017 7.4.6, 11.5.1), on the right-hand and the left-hand side.
module main(input clk, input [31:0] v, input [15:0] x, input [7:0] y);
  logic [3:0][7:0] a;     // descending
  logic [0:3][7:0] b;     // ascending
  logic [4:1][7:0] c;     // offset
  assign a = v;
  assign b = v;
  assign c = v;

  p0: assert property (@(posedge clk) a[0 +: 2] == v[15:0]);
  p1: assert property (@(posedge clk) a[3 -: 2] == v[31:16]);
  p2: assert property (@(posedge clk) a[1 +: 2] == a[2:1]);
  p3: assert property (@(posedge clk) b[0 +: 2] == v[31:16]);
  p4: assert property (@(posedge clk) b[3 -: 2] == v[15:0]);
  p5: assert property (@(posedge clk) c[1 +: 2] == v[15:0] && c[4 -: 1] == v[31:24]);

  logic [3:0][7:0] d;
  logic [0:3][7:0] e;
  always_comb begin
    d = 0; d[1 +: 2] = x;
    e = 0; e[2 -: 2] = x;
  end

  wire [4:1][7:0] w;
  assign w[1 +: 2] = x;
  assign w[4 -: 2] = 16'hABCD;

  logic [3:0][7:0] r = 0;
  always_ff @(posedge clk) r[3 -: 1] <= y;

  p6: assert property (@(posedge clk) d == {8'd0, x, 8'd0});
  p7: assert property (@(posedge clk) e == {8'd0, x, 8'd0});
  p8: assert property (@(posedge clk) w == {16'hABCD, x});
  p9: assert property (@(posedge clk) r[2:0] == 0);
  // fails
  p10: assert property (@(posedge clk) a[0 +: 2] == v[31:16]);
endmodule
