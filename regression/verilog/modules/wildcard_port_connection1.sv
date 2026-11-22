module M(input a, b);
  assert final (a);
  assert final (!b);
endmodule

module main;
  wire a = 1, b = 0;
  M m(.*);
endmodule
