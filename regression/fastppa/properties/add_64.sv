module main(input clk, input [63:0] a, b, output reg [63:0] q);
  always @(posedge clk) q <= a + b;
endmodule
