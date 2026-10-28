module main(input clk);
  reg x;
  initial x = 0;
  always @(posedge clk) x <= 1;
  p0: assert property (@(posedge clk) x == 1);
endmodule
