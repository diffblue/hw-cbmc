module main;

  // 1800-2017 5.7.1

  // "Unsized unsigned literal constants where the high-order bit is unknown
  // (X or x) or three-state (Z or z) shall be extended to the size of the
  // expression containing the literal constant."
  initial assert (('hx0 | 64'h0) === 64'hxxxx_xxx0);

  // z-extension
  initial assert ((1 ? 'hz0 : 64'h0) === 64'hzzzz_zzz0);

  // MSB is not x/z: zero-extension, not x-extension
  initial assert (('hF0 | 64'h0) === 64'h0000_00F0);

endmodule
