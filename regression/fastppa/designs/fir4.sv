module fir4(input clk, input signed [15:0] din,
            output reg signed [31:0] dout);
  reg signed [15:0] d1, d2, d3;
  parameter signed [15:0] C0 = 16'sd3;
  parameter signed [15:0] C1 = 16'sd7;
  parameter signed [15:0] C2 = 16'sd7;
  parameter signed [15:0] C3 = 16'sd3;
  always @(posedge clk) begin
    d1 <= din;
    d2 <= d1;
    d3 <= d2;
    dout <= din * C0 + d1 * C1 + d2 * C2 + d3 * C3;
  end
endmodule
