module adder_128(input clk, input [128-1:0] a, b, output reg [128-1:0] sum);
  always @(posedge clk) sum <= a + b;
endmodule
