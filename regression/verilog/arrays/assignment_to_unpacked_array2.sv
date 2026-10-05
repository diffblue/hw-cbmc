module main;

  // 1800 2017 7.6
  // "A fixed-size unpacked array ... shall be assignment compatible
  // with any other such array or slice if all the following conditions
  // are satisfied:
  // — The element types of source and target shall be equivalent.
  // — If the target is a fixed-size array or a slice, the source array
  // shall have the same number of elements as the target.

  int A[10:1];
  int C[24:1];

  initial A = C; // type check error: different sizes

endmodule
