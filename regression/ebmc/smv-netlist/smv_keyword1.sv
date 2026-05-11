module main(input clk);

  // MODULE is an SMV keyword
  reg MODULE;

  initial MODULE = 0;

  always @(posedge clk)
    MODULE = !MODULE;

  assert property (always s_eventually MODULE);

endmodule
