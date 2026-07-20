// this example is a representation of the circuit in
// "SAT-Based Verification without State Space Traversal"
//   by Per Bjesse & Koen Claessen (FMCAD 2000)
module main(clock, s3, out);
   input clock;
   input s3;
   output out;

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

   always @ (posedge clock) s4 <= ~s5;
   always @ (posedge clock) s7 <= ~s3;
   always @ (posedge clock) s8 <= s9;
   assign out=s11;
   // not inductive for any k
   p0: assert property (s11);
   p1: assert property ((s7 |~s4) & s11);
   // 3-inductive
   p2: assert property ((s8 |~s4) & s11);
   // 2-inductive
   p3: assert property ((~s8 | ~s7 | s4) & s11);
   p4: assert property ((s8 |~s4) & (s7 |~s4) & s11);
   p5: assert property ((s7 |~s4) & (~s8 | ~s7 | s4) & s11);
   p6: assert property ((s8 |~s4) & (~s8 | ~s7 | s4) & s11);
   // inductive
   p7: assert property ((s7 |~s4) & (s8 |~s4) & (~s8 | ~s7 | s4) & s11);
endmodule
