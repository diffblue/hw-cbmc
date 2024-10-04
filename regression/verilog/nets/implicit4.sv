module main;

  wire [3:0] A, B;

  // implicit nets are allowed on the LHS of a continuous assignment
  assign O = A & B;

  always assert final (O == (A & B));
  always assert final ($bits(O) == 4);

endmodule
