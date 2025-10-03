module main;

  initial assert ((4'b0000 ^ 4'b01zx) === 4'b01xx);
  initial assert ((4'b1111 ^ 4'b01zx) === 4'b10xx);
  initial assert ((4'bxxxx ^ 4'b01zx) === 4'bxxxx);
  initial assert ((4'bzzzz ^ 4'b01zx) === 4'bxxxx);

endmodule
