module main(input clk, input bad_in);

  reg [3:0] c = 0;
  reg bad;

  always @(posedge clk)
    c <= c + 1;

  always @(posedge clk)
    bad <= bad_in;

  a0: assume property (@(posedge clk) s_eventually[2:3] c == 3);
  p0: assert property (@(posedge clk) !bad);

endmodule
