module main;

  // 1800-2017 20.3.2: $realtime returns the current simulation time,
  // scaled to the time unit of the module that invokes it, as a real.
  initial p0: assert property (##0 $realtime == 0.0);
  initial p1: assert property (##1 $realtime == 1.0);
  initial p2: assert property (##2 $realtime == 2.0);

  initial p3: assert property (##2 $realtime > 1.5);

endmodule
