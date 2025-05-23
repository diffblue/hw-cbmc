module main(input clk);

  // count up
  int x = 0;

  always_ff @(posedge clk)
    x++;

  // passes with bound >=9
  p0: cover property (1[=10]);

  // passes with bound >=3
  p1: cover property (1[=4:10]);

  // passes with bound >=4
  p2: cover property (1[=5:10]);

endmodule
