module const_index(input clk, input [7:0] din, output reg [7:0] dout);
  reg [7:0] mem [0:7];
  always @(posedge clk) begin
    mem[3] <= din;
    dout <= mem[5];
  end
endmodule
