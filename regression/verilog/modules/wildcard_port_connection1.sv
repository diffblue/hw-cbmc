module M(input a, b);
  assert final (a);
  assert final (!b);
endmodule

module main;
  wire a = 0, b = 1;
  M m(.*);
endmodule
