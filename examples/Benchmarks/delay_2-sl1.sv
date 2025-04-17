module DELAY (input clk, input rst, output reg sig ,output reg err, output reg flg);
  localparam N = 1250;
  localparam CBITS = 11;
  reg [CBITS-1 :0] cnt;
  assign sig = (cnt >= N);
  assign err = (cnt > N);
  assign flg = (cnt < N);
  always @(posedge clk) begin
    if (rst || cnt >= N) cnt <= 0;
    else cnt <= cnt + 1; 
  end
    sl1: assert property (@(posedge clk) (always !rst) implies s_nexttime always (flg s_until sig));
    // (G !rst -> X G (flg U sig))
endmodule
