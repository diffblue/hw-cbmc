module large_array(input clk, input we, input [7:0] waddr, raddr,
                  input [31:0] wdata, output reg [31:0] rdata);
  reg [31:0] mem [0:255]; // 256 x 32 = 8192 bits, above the SRAM threshold
  always @(posedge clk) begin
    if (we)
      mem[waddr] <= wdata;
    rdata <= mem[raddr];
  end
endmodule
