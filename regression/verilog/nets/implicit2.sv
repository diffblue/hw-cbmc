module main;

  // implicit nets are allowed in the port connection list of a module
  and [3:0] (O, A, B);

  always assert final (O == (A & B));
  always assert final ($bits(O) == 4);

endmodule
