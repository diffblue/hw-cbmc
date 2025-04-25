module main(input clk);

  // count up
  int x = 0;

  always_ff @(posedge clk)
    x++;

  // expected to fail
  p0: cover property (x==2 ##1 x==3 ##1 x==100);

  // expected to fail until x reaches 100
  p1: cover property (x==98 ##1 x==99 ##1 x==100);

  // expected to pass once x reaches 5
  p2: cover property (x==3 ##1 x==4 ##1 x==5);

  // expected to pass once x reaches 6
  p3: cover property (x==4 ##1 x==5 ##1 x==6);

endmodule
