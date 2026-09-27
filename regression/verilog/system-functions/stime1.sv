module main;

  // 1800-2017 20.3.3: $stime returns the low-order 32 bits of the
  // current simulation time, as a 32-bit unsigned integer. The width
  // is 32 bits, and the value is nondeterministic.
  p0: assert property ($bits($stime) == 32);
  p1: assert property ($stime == 0);

endmodule
