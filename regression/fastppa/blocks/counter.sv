module counter(input clk);
  reg [7:0] cnt;
  initial cnt = 0;
  always @(posedge clk) cnt <= cnt + 1;
endmodule
