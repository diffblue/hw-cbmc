module main;

  // 1800-2017 5.7.1

  // "Unsized unsigned literal constants where the high-order bit is unknown
  // (X or x) or three-state (Z or z) shall be extended to the size of the
  // expression containing the literal constant."
  initial assert (('hx0 | 64'h0) === 64'hxxxx_xxx0);

endmodule
