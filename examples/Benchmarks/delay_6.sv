module DELAY (input clk, input rst, output reg sig ,output reg err, output reg flg);
  localparam N = 10000;
  localparam CBITS = 14;
  reg [CBITS-1 :0] cnt;
  assign sig = (cnt >= N);
  assign err = (cnt > N);
  assign flg = (cnt < N);
  always @(posedge clk) begin
    if (rst || cnt >= N) cnt <= 0;
    else cnt <= cnt + 1; 
  end
    p1: assert property (@(posedge clk) s_eventually !rst -> sig);
    // F G !rst -> G F sig
endmodule
