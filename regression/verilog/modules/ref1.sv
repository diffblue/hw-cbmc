module M(ref [31:0] some_ref);
  initial some_ref = 123;
endmodule

module main;
  bit [31:0] some_var;
  M m(some_var);
  assert final (some_var == 123);
endmodule
