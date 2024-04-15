module main;

  reg [31:0] x;
  wire clk;

  initial x=0;

  always @(posedge clk)
    x<=x+1;

  // holds owing to the range
  initial p0: assert property (always [0:9] x<10);

  // unbounded, fails
  initial p1: assert property (always [0:$] x<10);

  // strong variant
  initial p2: assert property (s_always [0:9] x<10);

endmodule
