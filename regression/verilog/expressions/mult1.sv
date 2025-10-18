module main;

  // Any arithmetic with x or z returns x.
  initial assert(32'bx * 0 === 32'hxxxx_xxxx);
  initial assert(32'bz * 0 === 32'hxxxx_xxxx);
  initial assert(0 * 32'bx === 32'hxxxx_xxxx);
  initial assert(0 * 32'bz === 32'hxxxx_xxxx);

endmodule
