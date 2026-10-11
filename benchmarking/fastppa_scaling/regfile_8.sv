module regfile_8(input clk, input we,
              input [3-1:0] raddr, waddr,
              input [31:0] wdata,
              output reg [31:0] rdata);
  reg [31:0] regs [0:8-1];
  always @(posedge clk) begin
    if (we)
      regs[waddr] <= wdata;
    rdata <= regs[raddr];
  end
endmodule
