module main(input a, b);

  p0: assert property ((always a) iff (always a));
  p1: assert property ((eventually[0:1] a) iff (eventually[0:1] a));
  p2: assert property ((s_eventually a) iff (s_eventually a));
  p3: assert property ((a until b) iff (a until b));
  // p4: assert property ((a s_until b) iff (a s_until a));
  p5: assert property ((a until_with b) iff (a until_with b));
  p6: assert property ((a s_until_with b) iff (a s_until_with a));

endmodule
