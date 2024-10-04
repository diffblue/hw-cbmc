module main;

  wire A, B;

  // implicit nets are allowed on the LHS of a continuous assignment
  assign O = A & B;

  always assert final (O == (A && B));

endmodule
