module main(input clk);

  reg [7:0] x = 0;

  // 0 1 2 3 4 ...
  always_ff @(posedge clk)
    x<=x+8'd1;

  // 0 0 1 1 2 2 3 3 ...
  wire [7:0] half_x = x/8'd2;

  // should pass
  initial p0: assert property (half_x==0[*2]);
  initial p1: assert property (half_x==0[->2]);
  initial p2: assert property (half_x==0[=2]);

  // should fail -- the repetition must be consecutive
  initial p3: assert property (x==0[*2]);

  // these pass, since the weak variant allows postponing satisfaction
  initial p4w: assert property (x==0[->2]);
  initial p5w: assert property (x==0[=2]);

  // these fail, since the strong variant requires the match
  initial p4s: assert property (strong(x==0[->2]));
  initial p5s: assert property (strong(x==0[=2]));

endmodule
