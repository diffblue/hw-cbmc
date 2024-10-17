module main;

  parameter P = 10;

  // implicit nets are allowed in the port connection list of a module
  sub #(P) my_sub(x);

  // The type of the implicit net is _not_ the type of the port,
  // but an "implicit scalar net of default net type".
  parameter Q = $bits(x);

  assert final (Q == 1);

endmodule

module sub #(parameter P = 1)(input [P:0] some_input);
endmodule
