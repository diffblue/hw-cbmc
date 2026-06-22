module idx_8(input clk, input [8-1:0] we, input [31:0] din,
                   input [3-1:0] raddr, output reg [31:0] rdata);
  reg [31:0] regs [0:8-1];
  integer i;
  always @(posedge clk) begin
    for (i = 0; i < 8; i = i + 1)
      if (we[i]) regs[i] <= din;
    rdata <= regs[raddr];
  end
endmodule
