module main;

  real t;

  // 1800-2017 20.3.1: $realtime returns the current simulation time,
  // scaled to the time unit of the module that invokes it, as a real.
  initial t = $realtime;

endmodule
