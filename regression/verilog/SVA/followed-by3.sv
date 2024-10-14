module main(input clk);

  reg [31:0] x;

  initial x=0;

  // 0, 1, ..., 10
  always @(posedge clk)
    if(x!=10)
      x<=x+1;

  // passes
  initial p0: assert property (x==0 ##1 x==1 #-# s_eventually x==10);
  initial p1: assert property (x==0 ##1 x==1 #=# s_eventually x==10);
  initial p2: assert property (x==0 ##1 x==1 #-# s_eventually x==2);

  // fails, we don't get to 11
  initial p3: assert property (x==0 ##1 x==1 #-# s_eventually x==11);

  // fails, we don't go back to 1
  initial p4: assert property (x==0 ##1 x==1 #=# s_eventually x==1);

  // fails owing to left hand side
  initial p5: assert property (x==0 ##1 x==2 #-# 1);

endmodule
