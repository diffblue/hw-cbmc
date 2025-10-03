module main;

  // Any arithmetic with x or z returns x.
  initial assert(-32'bz === 32'hxxxx_xxxx);

  // Downwards type propagation passes through unary minus.
  initial assert(-(1'sb1 + 1'sb1) == 2);

endmodule
