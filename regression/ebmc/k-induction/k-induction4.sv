module main(input clk);

  reg [31:0] x;
  
  initial x=0;
  
  always @(posedge clk)
    if(x != 10)
      x<=x+1;

  // true but not inductive
  p1: assert property (x[31] == 0);

endmodule
