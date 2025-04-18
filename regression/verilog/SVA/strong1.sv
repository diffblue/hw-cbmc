module main;

  reg [31:0] x;
  wire clk;

  initial x=0;

  always @(posedge clk)
    x<=x+1;

  // fails if bound is too low
  initial p0: assert property (strong(##[0:9] x==5));

endmodule
