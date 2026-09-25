module main;

  // 1800-2017 20.3.1: $time yields a 64-bit integer.
  // 1800-2017 20.3.3: $stime yields the low-order 32 bits, as a 32-bit
  // unsigned integer.
  // EBMC has no notion of continuous simulation time, so the result of
  // these functions is nondeterministic. We can, however, check the
  // widths of the results.
  p0: assert property ($bits($time) == 64);
  p1: assert property ($bits($stime) == 32);

  // The value is nondeterministic, and hence a property that fixes the
  // value must fail.
  p2: assert property ($time == 0);

endmodule
