module GRAY #(localparam CBITS = 12) (input clk, input rst, output reg [CBITS-1:0] gray_cnt, output reg sig);
  reg [CBITS-1:0] cnt;
  always@(posedge clk, posedge rst) begin
    if (rst) begin
      cnt = 0;
    end
    else begin
      cnt = cnt + 1;
      gray_cnt = (cnt) ^ ((cnt) >> 1);
      if(gray_cnt == 0)
        sig = 1;
      else
        sig = 0;
    end
  end
  p3: assert property (@(posedge clk) (always s_eventually rst == 1) or (always s_eventually (sig == 1 and s_eventually sig == 0))) ;
  // F G (rst = F) -> G F (sig = T & F (sig = F))
endmodule
