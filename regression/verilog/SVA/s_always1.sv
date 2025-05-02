module main(input clk);

  reg [31:0] x = 0;

  always_ff @(posedge clk)
    x<=x+1;

  // should pass
  initial p0: assert property (s_always [0:9] x<10);

  // should fail
  initial p1: assert property (not s_always [0:9] x<10);

endmodule
