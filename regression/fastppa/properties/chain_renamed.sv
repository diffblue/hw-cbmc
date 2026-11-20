module main(input clk, input [31:0] w, x, y, z, output reg [31:0] result);
  wire [31:0] partial = w + x;
  always @(posedge clk) result <= partial + y + z;
endmodule
