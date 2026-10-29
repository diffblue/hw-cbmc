module main(input clk);
  // $time is non-deterministic in every state
  wire [7:0] t = $time;
  p0: assert property (@(posedge clk) t != 5);
  p1: assert property (@(posedge clk) t == t);
endmodule
