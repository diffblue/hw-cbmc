module main(input clk, input a);

  reg my_bit;

  initial my_bit=0;

  always @(posedge clk)
    my_bit = !my_bit;

  // A plain-safety assumption. It requires no liveness-to-safety
  // translation, and should simply be kept as an assumption.
  assume property (always a);

  // expected to pass
  p0: assert property (s_eventually my_bit);

endmodule
