module main(input clk);

  reg [31:0] x;
  initial x = 1;

  always @(posedge clk)
    if(x<10)
      x<=x+1;

  p1: assert property (x>=$past(x));

endmodule
