module adder_64(input clk, input [64-1:0] a, b, output reg [64-1:0] sum);
  always @(posedge clk) sum <= a + b;
endmodule
