module parity(input clk, input [31:0] data, output reg parity_bit);
  always @(posedge clk) parity_bit <= ^data;
endmodule
