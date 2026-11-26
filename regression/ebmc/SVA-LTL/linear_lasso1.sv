module main(input clk);

  reg [1:0] c;

  initial c = 0;

  // 0 1 2 3 0 1 2 3 ...
  always @(posedge clk) c = c + 1;

  // fails, the counter never reaches 5
  p0: assert property (always (c == 2 implies s_eventually c == 5));

endmodule
