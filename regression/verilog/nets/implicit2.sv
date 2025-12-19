module main;

  // Implicit nets are allowed in the port connection list of a module.
  // The type of the implicit net is _not_ the type of the port,
  // but an "implicit scalar net of default net type".
  and my_instance[3:0] (O, A, B);

  always assert final (O == (A & B));
  always assert final ($bits(O) == 1);

endmodule
