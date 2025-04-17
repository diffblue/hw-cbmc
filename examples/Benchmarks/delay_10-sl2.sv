module DELAY (input clk, input rst, output reg sig ,output reg err, output reg flg);
  localparam N = 20000;
  localparam CBITS = 15;
  reg [CBITS-1 :0] cnt;
  assign sig = (cnt >= N);
  assign err = (cnt > N);
  assign flg = (cnt < N);
  always @(posedge clk) begin
    if (rst || cnt >= N) cnt <= 0;
    else cnt <= cnt + 1; 
  end
    sl2: assert property (@(posedge clk) (s_eventually always !rst) implies s_eventually always (flg s_until sig));
    // (FG !rst -> F G (flg U sig))
endmodule
