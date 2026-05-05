module main(input clk);

  reg [3:0] x = 0;

  // 0 1 2 3 4 ...
  always_ff @(posedge clk)
    x<=x+8'd1;

  // 0 0 1 1 2 2 3 3 ...
  wire [3:0] half_x = x/8'd2;

  // should pass
  initial p0: assert property (half_x==0[*2]);
  initial p1: assert property (half_x==0[->2]);
  initial p2: assert property (half_x==0[=2]);

  // should fail -- the repetition must be consecutive
  initial p3: assert property (x==0[*2]);

  // these pass, since the weak variant allows postponing satisfaction
  initial p4w: assert property (x==0[->2]);
  initial p5w: assert property (x==0[=2]);

  // these are proved up to bound (pending matches suffice for assert)
  initial p4s: assert property (strong(x==0[->2]));
  initial p5s: assert property (strong(x==0[=2]));

  // cover: no witness found (pending matches dropped for cover)
  initial c4s: cover property (strong(x==0[->2]));
  initial c5s: cover property (strong(x==0[=2]));

endmodule
