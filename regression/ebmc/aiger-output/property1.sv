module main(input clk);
  reg [1:0] cnt;
  initial cnt = 0;
  always @(posedge clk) cnt <= cnt + 1;
  p1: assert property (@(posedge clk) cnt != 3);
endmodule
