module main();
  // since Verilog-2005
  always assert p0: $clog2(0) == 0;
  always assert p1: $clog2(1) == 0;
  always assert p2: $clog2(2) == 1;
  always assert p3: $clog2(3) == 2;
  always assert p4: $clog2(4) == 2;
  always assert p5: $clog2(5) == 3;
  always assert p6: $clog2('h10000) == 16;

  // yields a compile-time constant
  wire [$clog2(64):1] some_wire;

endmodule
