module fir16(input clk, input signed [15:0] din, output reg signed [31:0] dout);
  reg signed [15:0] d0, d1, d2, d3, d4, d5, d6, d7;
  reg signed [15:0] d8, d9, d10, d11, d12, d13, d14, d15;
  always @(posedge clk) begin
    d0<=din; d1<=d0; d2<=d1; d3<=d2; d4<=d3; d5<=d4; d6<=d5; d7<=d6;
    d8<=d7; d9<=d8; d10<=d9; d11<=d10; d12<=d11; d13<=d12; d14<=d13; d15<=d14;
    dout <= d0*16'sd1 + d1*16'sd3 + d2*16'sd7 + d3*16'sd15 +
            d4*16'sd28 + d5*16'sd45 + d6*16'sd60 + d7*16'sd70 +
            d8*16'sd70 + d9*16'sd60 + d10*16'sd45 + d11*16'sd28 +
            d12*16'sd15 + d13*16'sd7 + d14*16'sd3 + d15*16'sd1;
  end
endmodule
