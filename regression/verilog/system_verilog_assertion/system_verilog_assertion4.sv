module main(input clk);

  reg [31:0] x, y;

  initial x=0;
  initial y=0;

  always @(posedge clk) x<=x+1;
  always @(posedge clk) y<=y+2;

  p1:  assert property (x==0 |-> y==0);
  p2:  assert property (x==0 |-> not x==1);
  p3:  assert property (x==0 |=> y==2);
  p4:  assert property (x==0 |-> ##0 x==0 ##1 x==1 ##5 x==6);
  p5:  assert property (x==0 |-> y==0 ##1 y==2);
  p6:  assert property (x==0 |-> y==0 ##1 y==2 ##1 y==4);
  p7:  assert property (x==0 |-> ##1 x==1);
  p8:  assert property (x==1 |-> ##[1:10] y==20);
  p9:  assert property (x==0 |-> ##[1:$] y==18);
  p10: assert property (x==0 |-> ##1 x==1 and ##2 x==2);
  p11: assert property (x==0 |-> ##1 x==1 and not ##2 x==3);
  p12: assert property (x==0 |-> ##1 x==1 && y==2);

endmodule
