module main(input a, b);

  p0: assert property ((always a) implies (always a));
  p1: assert property ((a or (always b)) implies (a or (always b)));
  p2: assert property ((eventually[0:1] a) implies (eventually[0:1] a));
  p3: assert property ((s_eventually a) implies (s_eventually a));
  p4: assert property ((a until b) implies (a until b));
  // p5: assert property ((a s_until b) implies (a s_until a));
  p6: assert property ((a until_with b) implies (a until_with b));
  p7: assert property ((a s_until_with b) implies (a s_until_with a));

endmodule
