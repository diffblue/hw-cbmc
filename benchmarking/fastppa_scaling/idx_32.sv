module idx_32(input clk, input [32-1:0] we, input [31:0] din,
                   input [5-1:0] raddr, output reg [31:0] rdata);
  reg [31:0] regs [0:32-1];
  integer i;
  always @(posedge clk) begin
    for (i = 0; i < 32; i = i + 1)
      if (we[i]) regs[i] <= din;
    rdata <= regs[raddr];
  end
endmodule
