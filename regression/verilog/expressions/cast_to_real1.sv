module main;

  // No rounding.
  p0: assert final (real'(0) == 0.0);
  p1: assert final (real'(1) == 1.0);

  // Rounding. The standard does not say how.  This is RNA.
  // Icarus Verilog, Aldec Riviera, Questa, VCS agree.
  // Cadence Xcelium disagrees.
  p2: assert final (real'('hffff_ffff_ffff_ffff) == real'('h1_0000_0000_0000_0000));

endmodule
