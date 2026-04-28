module main;

  reg [31:0] x;
  wire clk;

  initial x=0;

  always @(posedge clk)
    x<=x+1;

  // proved up to bound if bound is too low
  initial p0: assert property (strong(##[0:9] x==5));

  // cover: no witness found within bound
  initial c0: cover property (strong(##[0:9] x==5));

endmodule
