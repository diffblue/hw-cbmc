module main(input clk);

  // no initial state constraint on my_bit
  reg my_bit;

  always @(posedge clk)
    my_bit = my_bit;

  // expected to fail
  p0: assert property (my_bit == 0);

endmodule
