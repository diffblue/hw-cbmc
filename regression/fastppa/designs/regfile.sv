module regfile(input clk, input we,
              input [4:0] raddr1, raddr2, waddr,
              input [31:0] wdata,
              output reg [31:0] rdata1, rdata2);
  reg [31:0] regs [0:31];
  always @(posedge clk) begin
    if (we)
      regs[waddr] <= wdata;
    rdata1 <= regs[raddr1];
    rdata2 <= regs[raddr2];
  end
endmodule
