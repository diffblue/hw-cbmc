module main;

  // Any arithmetic with x or z returns x.
  initial assert(-32'bz === 32'hxxxx_xxxx);

endmodule
