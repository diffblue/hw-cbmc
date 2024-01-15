module main(input clk);

  reg [31:0] x;
  
  initial x=1;
  
  always @(posedge clk)
    if(x<10)
      x<=x+1;

  // true, but not supported by k-induction
  p0: assert property (eventually x == 10);

  // true and supported by k-induction
  p1: assert property (x<=10);

endmodule
