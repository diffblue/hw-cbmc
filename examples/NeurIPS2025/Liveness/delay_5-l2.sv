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

  // LTLSPEC F G (Verilog.DELAY.rst = FALSE) -> G F (Verilog.DELAY.sig = TRUE & X Verilog.DELAY.sig = FALSE)
  assert property (@(posedge clk) s_eventually (!rst implies (sig and s_nexttime !sig)));

endmodule