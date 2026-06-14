module main(input clk);

  // count up
  int x = 0;

  always_ff @(posedge clk)
    x++;

  // Equivalent to 'true' within the relevant time period,
  // but 'true' would be simplified by Spot,
  // and this isn't.
  wire c = x != 1000;

  // passes with bound >=9
  p0: cover sequence (c[=10]);

  // passes with bound >=3
  p1: cover sequence (c[=4:10]);

  // passes with bound >=4
  p2: cover sequence (c[=5:10]);

endmodule
