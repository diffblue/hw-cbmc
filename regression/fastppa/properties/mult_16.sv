module main(input clk, input [15:0] a, b, output reg [15:0] q);
  always @(posedge clk) q <= a * b;
endmodule
