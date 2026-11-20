module main(input clk, input [31:0] a, b, output reg [31:0] q);
  reg [31:0] unused;
  always @(posedge clk) begin q <= a + b; unused <= a * b; end
endmodule
