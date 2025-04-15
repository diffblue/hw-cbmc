module main(input clk);

  reg x;

  initial x = 0;

  always @(posedge clk)
    x = !x;

  assert property (always s_eventually x);

  // won't get translated
  assert property (x[->5]);

endmodule
