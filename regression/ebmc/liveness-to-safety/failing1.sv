module main(input clk);

  reg my_bit;

  initial my_bit=0;

  always @(posedge clk)
    my_bit = 0;

  // expected to fail
  p0: assert property (eventually my_bit);

endmodule
