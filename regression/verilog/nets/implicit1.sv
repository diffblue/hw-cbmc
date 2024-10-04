module main;

  // implicit nets are allowed in the port connection list of a module
  and (O, A, B);

  always assert final (O == (A && B));

endmodule
