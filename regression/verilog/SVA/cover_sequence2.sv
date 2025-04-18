module main(input clk);

  // count up
  reg [7:0] x = 0;

  always @(posedge clk)
    x++;

  // expected to fail
  p0: cover property (x==2 ##1 x==3 ##1 x==100);

  // expected to fail until bound reaches 100
  p1: cover property (x==98 ##1 x==99 ##1 x==100);

endmodule
