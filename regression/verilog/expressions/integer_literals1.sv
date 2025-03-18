module main;

  p01: assert final ($bits(8'b1)==8);

  // 1800-2017 5.7.1L without a given width, the number of bits "shall be at least 32"
  p02: assert final ($bits(1)==32);
  p03: assert final ($bits('d1)==32);
  p04: assert final ($bits('b1)==32);

  // simple decimal numbers without size and base are signed
  p05: assert final ($typename(1)=="bit signed[31:0]");

  // numbers with size or base are unsigned
  p06: assert final ($typename('d1)=="bit[31:0]");
  p07: assert final ($typename(10'd1)=="bit[9:0]");

  // unbased unsized literals
  p08: assert final ($typename('0)=="bit[0:0]" && '0===1'b0);
  p09: assert final ($typename('1)=="bit[0:0]" && '1===1'b1);
  p10: assert final ($typename('x)=="logic[0:0]" && 'x===1'bx);
  p11: assert final ($typename('z)=="logic[0:0]" && 'z===1'bz);

  // decimals must not contain x/z "unless there is
  // exactly one digit in the token"
  p12: assert final ('dx===32'hxxxx_xxxx);
  p13: assert final ('dX===32'hxxxx_xxxx);
  p14: assert final ('dz===32'hzzzz_zzzz);
  p15: assert final ('dZ===32'hzzzz_zzzz);
  p16: assert final (4'dx===4'hx);
  p17: assert final (4'dX===4'hx);
  p18: assert final (4'dz===4'hz);
  p19: assert final (4'dZ===4'hz);
  p20: assert final ($typename(4'sdx)==="logic signed[3:0]");

endmodule
