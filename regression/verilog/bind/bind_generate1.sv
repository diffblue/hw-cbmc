module observer(input clk, input [7:0] cnt);
  p0: assert property (@(posedge clk) cnt != 8'd3);
endmodule

module counter(input clk);
  reg [7:0] cnt;
  initial cnt = 0;
  always @(posedge clk) cnt = cnt + 1;
endmodule

module main(input clk);
  parameter WITH_CHECKS = 1;

  // IEEE 1800-2017 23.11
  // The bind directive in the taken generate branch is applied,
  // the one in the untaken branch is not.
  if (WITH_CHECKS) begin : yes
    bind counter observer obs(.clk(clk), .cnt(cnt));
  end

  if (!WITH_CHECKS) begin : no
    bind counter observer obs2(.clk(clk), .cnt(cnt));
  end

  counter c(clk);
endmodule
