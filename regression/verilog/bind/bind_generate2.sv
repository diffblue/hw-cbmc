module observer(input clk, input [7:0] cnt);
  p0: assert property (@(posedge clk) cnt != 8'd3);
endmodule

module main(input clk);
  reg [7:0] cnt;
  initial cnt = 0;
  always @(posedge clk) cnt = cnt + 1;

  parameter WITH_CHECKS = 1;

  // IEEE 1800-2017 23.11
  // A bind directive targeting the enclosing module;
  // the instantiation is added in place.
  if (WITH_CHECKS) begin : checks
    bind main observer obs(.clk(clk), .cnt(cnt));
  end
endmodule
