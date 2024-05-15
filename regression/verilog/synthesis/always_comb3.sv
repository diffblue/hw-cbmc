module main(input clk);
  reg q;
  
  reg w;

  // ff
  always @(posedge clk)
    q = !q;

  always_comb
    w = q;

  p1: assert property (@(posedge clk) w == q);

endmodule
