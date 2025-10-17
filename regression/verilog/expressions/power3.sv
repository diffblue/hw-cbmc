module main;

  // Any arithmetic with x or z returns x.
  initial assert('bx ** 1 === 'x);
  initial assert('bz ** 1 === 'x);
  initial assert(1 ** 'bx === 'x);
  initial assert(1 ** 'bz === 'x);

endmodule
