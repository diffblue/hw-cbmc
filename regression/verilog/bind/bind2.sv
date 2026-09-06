module observer #(parameter LIMIT = 1) (input clk, input [7:0] cnt);
  p0: assert property (@(posedge clk) cnt <= LIMIT);
endmodule

module counter(input clk);
  reg [7:0] cnt;
  initial cnt = 0;
  always @(posedge clk) cnt = cnt + 1;
endmodule

module aux(input clk);
  // IEEE 1800-2017 23.11
  // A bind directive as a module item, with a parameter assignment.
  bind counter observer #(.LIMIT(100)) obs(.clk(clk), .cnt(cnt));
endmodule

module main(input clk);
  aux a(clk);
  counter c(clk);
endmodule
