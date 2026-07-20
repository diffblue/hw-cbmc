module main(input clk, s3, output out);

  wire   s5=  s4 | s3;
  wire   s6= ~s4 |~s3;
  wire   s9= ~s8 |~s7;
  wire   s10= s9 |~s3;
  wire   s11=(~s6 | s10)&( s6 |~s10);

  reg    s4;
  reg    s7;
  reg    s8;

  initial s4=0;
  initial s7=0;
  initial s8=0;

  always @ (posedge clk) s4 <= ~s5;
  always @ (posedge clk) s7 <= ~s3;
  always @ (posedge clk) s8 <= s9;
  assign out=s11;

  // not inductive for any k
  p0: assert property (s11);

endmodule
