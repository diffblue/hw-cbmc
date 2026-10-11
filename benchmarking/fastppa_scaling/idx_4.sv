module idx_4(input clk, input [4-1:0] we, input [31:0] din,
                   input [2-1:0] raddr, output reg [31:0] rdata);
  reg [31:0] regs [0:4-1];
  integer i;
  always @(posedge clk) begin
    for (i = 0; i < 4; i = i + 1)
      if (we[i]) regs[i] <= din;
    rdata <= regs[raddr];
  end
endmodule
