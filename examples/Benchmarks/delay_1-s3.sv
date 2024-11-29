module DELAY (input clk, input rst, output reg sig ,output reg err, output reg flg);
  localparam N = 750;
  localparam CBITS = 10;
  reg [CBITS-1 :0] cnt;
  always @(posedge clk) begin
    if (rst) cnt = 0;
    else cnt = cnt + 1;
    if (cnt > N) begin sig = 1;
      cnt = 0; end
    else sig = 0;
    if (cnt > N + 1) err = 1;
    else err = 0;
    if (cnt <= N) flg = 1;
    else flg = 0;
  end
  s3: assert property (@(posedge clk) (nexttime always err == 0)) ;
  // X G Verilog.DELAY.err = FALSE
endmodule
