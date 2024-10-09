module main(input clk);

  reg [31:0] x = 0;

  // 0 1 2 3 4 ...
  always_ff @(posedge clk)
    x<=x+1;

  // 0 0 1 1 2 2 3 3 ...
  wire [31:0] half_x = x/2;

  // should pass
  initial p0: assert property (x==0[*]);
  initial p1: assert property (x==1[*]);
  initial p2: assert property (x==0[+] #-# x==1);
  initial p3: assert property (x==0[+]);
  initial p4: assert property (half_x==0[*]);

  // should fail
  initial p5: assert property (x==1[+]);
  initial p6: assert property (x==0[+] #=# x==1);

endmodule
