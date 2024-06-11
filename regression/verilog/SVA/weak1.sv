module main;

  reg [31:0] x;
  wire clk;

  initial x=0;

  always @(posedge clk)
    x<=x+1;

  // fails
  initial p0: assert property (weak(##[0:9] x==100));

endmodule
