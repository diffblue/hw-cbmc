module main;

  // 1800 2017 7.6
  // "A fixed-size unpacked array ... shall be assignment compatible
  // with any other such array or slice if all the following conditions
  // are satisfied:
  // — The element types of source and target shall be equivalent.
  // — If the target is a fixed-size array or a slice, the source array
  // shall have the same number of elements as the target.

  typedef struct {
    int i;
  } some_unpacked_struct;

  int A[10:1];
  some_unpacked_struct B[10:1];

  initial A = B; // error: same size, but element not compatible

endmodule
