module main;

  // 's' is a scalar (single-bit) variable: a reg with no packed
  // dimension.  It is *not* a vector.
  reg s = 1'b1;

  // 1800-2017 11.5.1 "Vector bit-select and part-select addressing":
  //   "A bit-select or part-select of a scalar, or of a real variable
  //    or real parameter, shall be illegal."
  // Hence the part-select s[0:0] is illegal and must be rejected
  // during type-checking.
  p0: assert final (s[0:0] == 1'b1);

endmodule
