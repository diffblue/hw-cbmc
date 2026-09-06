module observer(input clk, input [7:0] cnt);
  p0: assert property (@(posedge clk) cnt != 8'd3);
endmodule

module counter(input clk);
  reg [7:0] cnt;
  initial cnt = 0;
  always @(posedge clk) cnt = cnt + 1;
endmodule

module main(input clk);
  counter c1(clk);
  counter c2(clk);
endmodule

// IEEE 1800-2017 23.11
// The bind directive applies to instance c1 only, not to c2.
bind main.c1 observer obs(.clk(clk), .cnt(cnt));
