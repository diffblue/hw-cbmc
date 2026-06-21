module GRAY #(localparam CBITS = 12) (input clk, input rst, output reg [CBITS-1:0] gray_c, output reg sig, output reg flg);
  reg [CBITS-1:0] cnt;
  assign sig = (cnt == 0) & ~rst;
  assign flg = (cnt >= 0);
  always@(posedge clk, posedge rst) begin
    if (rst)
      cnt <= 0;
    else begin
      cnt <= cnt + 1;
      gray_c = (cnt) ^ ((cnt) >> 1);
    end
  end

  // LTLSPEC X G ((Verilog.GRAY.sig = TRUE & Verilog.GRAY.rst = FALSE) -> X Verilog.GRAY.sig = FALSE)
  assert property (@(posedge clk) sig && !rst |=> !sig);

endmodule
