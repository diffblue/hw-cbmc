module DELAY (input clk, input rst, output reg sig ,output reg err, output reg flg);
  localparam N = 7500;
  localparam CBITS = 13;
  reg [CBITS-1 :0] cnt;
  assign sig = (cnt >= N);
  assign err = (cnt > N);
  assign flg = (cnt < N);
  always @(posedge clk) begin
    if (rst || cnt >= N) cnt <= 0;
    else cnt <= cnt + 1; 
  end

  // LTLSPEC F G (Verilog.DELAY.rst = FALSE) -> F G ((Verilog.DELAY.flg = TRUE) U (Verilog.DELAY.sig = TRUE))
  assert property (@(posedge clk) (s_eventually always !rst) implies s_eventually always (flg s_until sig));

endmodule