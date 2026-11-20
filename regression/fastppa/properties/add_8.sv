module main(input clk, input [7:0] a, b, output reg [7:0] q);
  always @(posedge clk) q <= a + b;
endmodule
