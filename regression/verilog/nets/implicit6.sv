module main;

  parameter P = 2;

  // implicit nets are allowed in the port connection list of a module
  and [P:0] (O, A, B);

  assert final ($bits(O) == P+1);

endmodule
