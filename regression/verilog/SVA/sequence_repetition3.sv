module main(input clk);

  reg [31:0] x = 0;

  // 0 1 2 3 4 ...
  always_ff @(posedge clk)
    x<=x+1;

  // 0 0 1 1 2 2 3 3 ...
  wire [31:0] half_x = x/2;

  // should pass
  initial p0: assert property (x==0[*1] #=# x==1[*1]);
  initial p1: assert property (half_x==0[*2] #=# half_x==1[*2]);

  // should fail
  initial p2: assert property (half_x==0[*3]);

endmodule
