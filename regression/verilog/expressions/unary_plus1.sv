module main;

  // Any arithmetic with x or z normally returns x.
  // IVerilog, VCS, Questa, Riviera say that +'bz is z.
  // XCelium says it's 'x.

  // 1800-2017 11.4.3 says "For the arithmetic operators, if any operand bit
  // value is the unknown value x or the high-impedance value z, then the
  // entire result value shall be x."
  // But it also says "Unary plus m (same as m)" in Table 11-5.

  initial assert(+32'bz === 32'hxxxx_xxxx);

endmodule
