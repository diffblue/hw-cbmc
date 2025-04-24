module main;

  reg [31:0] x;
  wire clk;

  initial x=0;

  always @(posedge clk)
    if(x != 5)
      x<=x+1;

  // does not match -- passes
  initial p0: assert property (weak(##[0:$] x==10));

  // does not match -- fails
  initial p1: assert property (strong(##[0:$] x==10));

endmodule
