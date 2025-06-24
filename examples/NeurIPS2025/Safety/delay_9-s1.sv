module DELAY (input clk, input rst, output reg sig ,output reg err, output reg flg);
  localparam N = 17500;
  localparam CBITS = 15;
  reg [CBITS-1 :0] cnt;
  assign sig = (cnt >= N);
  assign err = (cnt > N);
  assign flg = (cnt < N);
  always @(posedge clk) begin
    if (rst || cnt >= N) cnt <= 0;
    else cnt <= cnt + 1; 
  end

  // LTLSPEC X G Verilog.DELAY.err = FALSE
  assert property (@(posedge clk) ##1 !err);

endmodule