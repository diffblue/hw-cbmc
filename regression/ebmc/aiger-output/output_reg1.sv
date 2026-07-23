module main(input clk, input x, output reg q);
  initial q = 0;
  always @(posedge clk) q <= x;
endmodule
