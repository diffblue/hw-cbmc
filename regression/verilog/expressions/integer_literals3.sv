module main;

  // 1800-2017 5.7.1

  // "All bits of the unsized value shall be set to the value of the specified
  // bit."
  initial assert ((1 ? '0 : 16'h0) === 16'h0000);
  initial assert ((1 ? '1 : 16'h0) === 16'hffff);
  initial assert ((1 ? 'x : 16'h0) === 16'hxxxx);
  initial assert ((1 ? 'z : 16'h0) === 16'hzzzz);

  initial assert ($bits(1 ? '0 : 16'h0) === 16);
  initial assert ($bits(1 ? '1 : 16'h0) === 16);
  initial assert ($bits(1 ? 'x : 16'h0) === 16);
  initial assert ($bits(1 ? 'z : 16'h0) === 16);

endmodule
