module main(input clk);

  reg [31:0] x;
  
  initial x=1;
  
  always @(posedge clk)
    if(x<10)
      x<=x+1;

  // true, but not supported by k-induction
  p0: assert property (s_eventually x == 10);

endmodule
