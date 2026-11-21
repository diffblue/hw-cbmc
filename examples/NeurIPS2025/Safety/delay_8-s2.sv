module DELAY (input clk, input rst, output reg sig ,output reg err, output reg flg);
  localparam N = 15000;
  localparam CBITS = 14;
  reg [CBITS-1 :0] cnt;
  assign sig = (cnt >= N);
  assign err = (cnt > N);
  assign flg = (cnt < N);
  always @(posedge clk) begin
    if (rst || cnt >= N) cnt <= 0;
    else cnt <= cnt + 1; 
  end

  // LTLSPEC G (Verilog.DELAY.sig = TRUE -> X Verilog.DELAY.sig = FALSE)
  assert property (@(posedge clk) sig |=> !sig);

endmodule