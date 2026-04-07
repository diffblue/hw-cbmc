module main;

  wire [3:0] A, B;

  // implicit nets are allowed on the LHS of a continuous assignment
  assign O = A & B;

  always assert final (O == (A & B & 1'b1));
  always assert final ($bits(O) == 1);

endmodule
