module adder_32(input clk, input [32-1:0] a, b, output reg [32-1:0] sum);
  always @(posedge clk) sum <= a + b;
endmodule
