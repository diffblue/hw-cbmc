module main(input clk, input [31:0] a, b, output reg [31:0] q, r);
  wire [31:0] p = a * b;
  always @(posedge clk) begin q <= p; r <= p; end
endmodule
