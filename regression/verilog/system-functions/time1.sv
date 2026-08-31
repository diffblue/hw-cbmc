module main;

  // 1800-2017 20.3.1: $time returns the current simulation time,
  // scaled to the time unit of the module that invokes it, as a
  // 64-bit integer.  EBMC's model of time is the sequence of
  // timeframes, i.e., time advances by one time unit per timeframe.
  initial p0: assert property (##0 $time == 0);
  initial p1: assert property (##1 $time == 1);
  initial p2: assert property (##2 $time == 2);
  initial p3: assert property (##3 $time == 3);

  // the width of the result is 64 bits
  p4: assert property ($bits($time) == 64);

  // this one fails, as the time advances
  initial p5: assert property (##2 $time == 0);

endmodule
