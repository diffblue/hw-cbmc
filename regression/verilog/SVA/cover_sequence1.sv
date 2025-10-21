module main(input clk);

  // count up
  reg [7:0] x = 0;

  always @(posedge clk)
    x++;

  // expected to pass
  p0: cover sequence (x==2 ##1 x==3 ##1 x==4);

  // expected to fail
  p1: cover sequence (x==2 ##1 x==3 ##1 x==5);

endmodule
