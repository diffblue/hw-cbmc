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
    s1: assert property (@(posedge clk) ##1 !err);
    // X G !err
endmodule
