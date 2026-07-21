module main;

  bit my_array0[32];
  int some_int;

  // this is an error -- unpacked arrays do not decay to an integral
  initial some_int = my_array0;

endmodule
