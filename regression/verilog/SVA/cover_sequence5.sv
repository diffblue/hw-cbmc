module main(input clk);

  // count up
  int x = 0;

  always_ff @(posedge clk)
    x++;

  // never passes, owing to disable iff
  p0: cover sequence (disable iff (1) 1);

  // passes when reaching x=10
  p1: cover sequence (disable iff (x<10) 1);

endmodule
