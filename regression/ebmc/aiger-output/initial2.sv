// https://github.com/diffblue/hw-cbmc/issues/2350
module top(input wire clk, input wire d, output reg q);
  initial q = 1'b1;
  always @(posedge clk) q <= d;
endmodule
