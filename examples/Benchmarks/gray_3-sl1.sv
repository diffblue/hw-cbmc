module GRAY #(localparam CBITS = 10) (input clk, input rst, output reg [CBITS-1:0] gray_c, output reg sig, output reg flg);
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
    sl1: assert property (@(posedge clk) (always !rst) implies s_nexttime always (cnt>0 s_until sig));
    // (G !rst -> X G (cnt > 0 U sig))
endmodule
