module main;

  // 1800-2017 11.5.1 "Vector bit-select and part-select addressing":
  // "It shall be legal for the ranges of a vector to be a negative
  //  number."  Here v has bit indices -8 .. 7, so v[-8] is the
  //  least-significant bit and v[-8..7] are all legal, in-range
  //  bit-selects (negative offsets into the vector are permitted).
  logic [7:-8] v = 16'h0001;

  p0: assert final (v[-8] == 1'b1);  // LSB
  p1: assert final (v[-7] == 1'b0);
  p2: assert final (v[7]  == 1'b0);  // MSB

endmodule
