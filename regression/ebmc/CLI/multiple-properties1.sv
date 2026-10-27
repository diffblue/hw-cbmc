module main(input clk, input x);
  p0: assert property (@(posedge clk) 1);
  p1: assert property (@(posedge clk) x);
  p2: assert property (@(posedge clk) 1);
endmodule
