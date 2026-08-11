module adder(input clk, input [31:0] a, b, output reg [31:0] sum);
  always @(posedge clk) sum <= a + b;
endmodule
