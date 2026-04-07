module main;

  initial assert ((4'b0000 & 4'b01zx) === 4'b0000);
  initial assert ((4'b1111 & 4'b01zx) === 4'b01xx);
  initial assert ((4'bxxxx & 4'b01zx) === 4'b0xxx);
  initial assert ((4'bzzzz & 4'b01zx) === 4'b0xxx);

endmodule
