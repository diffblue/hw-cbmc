module main;

  // Test for 1800-2017 11.2.1 Constant expressions
  // Following the order in 1800-2017 Table 11-1
  parameter p01 = 1?2:3;
  parameter p02 = +1;
  parameter p03 = -1;  
  parameter p04 = !0;
  parameter p05 = ~1;
  parameter p06 = &1;
  parameter p07 = ~&1;
  parameter p08 = |1;
  parameter p09 = ~|1;
  parameter p10 = ^1;
  parameter p11 = ~^1;
  parameter p12 = ^~1;
  parameter p13 = 1+1;
  parameter p14 = 1-1;
  parameter p15 = 1*1;
  parameter p16 = 1/1;
  parameter p17 = 1**1;
  parameter p18 = 1%1;
  parameter p19 = 1&1;
  parameter p20 = 1|1;
  parameter p21 = 1^1;
//  parameter p22 = 1^~1;
//  parameter p23 = 1~^1;
  parameter p24 = 1>>1;
  parameter p25 = 1<<1;
  parameter p26 = 1>>>1;
  parameter p27 = 1<<<1;
  parameter p28 = 1&&1;
  parameter p29 = 1||1;
  parameter p30 = 1->1;
//  parameter p31 = 1<->1;
  parameter p32 = 1<1;
  parameter p33 = 1<=1;
  parameter p34 = 1>1;
  parameter p35 = 1>=1;
//  parameter p36 = 1===1;
//  parameter p37 = 1!==1;
  parameter p38 = 1==1;
  parameter p39 = 1!=1;
//  parameter p40 = 1==?1;
//  parameter p41 = 1!=?1;
//  parameter p42 = 1 inside {1};
  parameter p43 = {1'b1, 1'b0};
  parameter p44 = {2{1'b1}};
//  parameter p45 = {<<{3'b101}};
//  parameter p46 = {>>{3'b101}};

endmodule
