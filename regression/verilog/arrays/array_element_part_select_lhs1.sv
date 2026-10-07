module main(input clk, input [3:0] wen, input [1:0] addr, input [31:0] wdata);

  reg [31:0] mem [0:3];

  initial begin
    mem[0] = 0; mem[1] = 0; mem[2] = 0; mem[3] = 0;
  end

  // 1800-2017 7.4.6: a part-select of an array element
  // is a valid lvalue; a byte-enabled write.
  always @(posedge clk) begin
    if (wen[0]) mem[addr][ 7: 0] <= wdata[ 7: 0];
    if (wen[1]) mem[addr][15: 8] <= wdata[15: 8];
    if (wen[2]) mem[addr][23:16] <= wdata[23:16];
    if (wen[3]) mem[addr][31:24] <= wdata[31:24];
  end

  // The bytes not enabled stay zero.
  p0: assert property (wen == 4'b0001 && addr == 0 && mem[0][31:8] == 0 |-> ##1 mem[0][31:8] == 0);

endmodule
