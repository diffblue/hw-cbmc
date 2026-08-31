module main;

  // 1800-2017 20.3.3: $stime returns the low-order 32 bits of the
  // current simulation time, as a 32-bit unsigned integer.
  initial p0: assert property (##0 $stime == 0);
  initial p1: assert property (##1 $stime == 1);
  initial p2: assert property (##2 $stime == 2);

  // the width of the result is 32 bits
  p3: assert property ($bits($stime) == 32);

  // $stime and $time agree while the time is small
  initial p4: assert property (##3 $stime == $time);

endmodule
