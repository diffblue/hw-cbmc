module main(input clk, input [7:0] a, output [7:0] y);
  real r;
  always @(posedge clk) r <= r * 2.0 + a;
  assign y = a;
endmodule
