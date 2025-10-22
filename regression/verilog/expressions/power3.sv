module main;

  // Any arithmetic with x or z returns x.
  initial assert('bx ** 1 === 32'hxxxx_xxxx);
  initial assert('bz ** 1 === 32'hxxxx_xxxx);
  initial assert(1 ** 'bx === 32'hxxxx_xxxx);
  initial assert(1 ** 'bz === 32'hxxxx_xxxx);

endmodule
