module main;

  reg [31:0] x;
  wire clk;

  initial x=0;

  always @(posedge clk)
    if(x != 5)
      x<=x+1;

  // does not match -- passes
  initial p0: assert property (weak(##[0:$] x==10));

  // does not match -- proved up to bound (pending match)
  initial p1: assert property (strong(##[0:$] x==10));

  // cover: no witness found
  initial c0: cover property (strong(##[0:$] x==10));

endmodule
