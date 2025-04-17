module GRAY #(localparam CBITS = 8) (input clk, input rst, output reg [CBITS-1:0] gray_c, output reg sig, output reg flg);
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
    sl2: assert property (@(posedge clk) (s_eventually always !rst) implies s_eventually always (flg s_until sig));
    // (FG !rst -> F G (flg U sig))
endmodule
