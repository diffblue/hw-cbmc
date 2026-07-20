module main(input clk);

  reg my_bit;

  initial my_bit=0;

  always @(posedge clk)
    my_bit = !my_bit;

  // no support for assumptions
  p0: assume property (my_bit == 0);

endmodule
