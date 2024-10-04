module main;

  // implicit nets are not allowed on the RHS of a continuous assignment
  assign O = A & B;

endmodule
