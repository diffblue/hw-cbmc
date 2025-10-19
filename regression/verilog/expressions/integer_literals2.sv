module main;

  // 1800-2017 5.7.1

  // "If the size of the unsigned number is smaller than the size specified
  // for the literal constant, the unsigned number shall be padded to the
  // left with zeros."
  initial assert (4'b1 === 4'b0001);

  // "If the leftmost bit in the unsigned number is an x or a z, then
  // an x or a z shall be used to pad to the left, respectively."
  initial assert (4'bz1 === 4'bzzz1);
  initial assert (4'bx1 === 4'bxxx1);

  // "If the size of the unsigned number is larger than the size specified
  // for the literal constant, the unsigned number shall be truncated from
  // the left."
  initial assert (4'b1111_1111 === 4'b1111);

endmodule
