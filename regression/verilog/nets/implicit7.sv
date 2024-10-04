module main;

  parameter P = 10;

  // implicit nets are allowed in the port connection list of a module
  sub #(P) my_sub(x);

  // The type of the implict net could be used to define another parameter
  parameter Q = $bits(x);

  assert final (Q == P + 1);

endmodule

module sub #(parameter P = 1)(input [P:0] some_input);
endmodule
