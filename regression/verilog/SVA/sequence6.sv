module main;

  reg [31:0] x;
  wire clk;

  initial x=0;

  always @(posedge clk)
    x<=x+1;

  // passes
  initial p0: assert property ((1 ##1 1) |-> x==1);

endmodule
