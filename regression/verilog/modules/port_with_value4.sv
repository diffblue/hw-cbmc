module M(input [31:0] a = 1, b = 2, c = 3);

  eq_a: assert final (a == 4);
  eq_b: assert final (b == 5);
  eq_c: assert final (c == 6);

endmodule

module main;
  // should pass
  M m1(4, 5, 6);

  // should fail -- b will be 2
  M m2(4, , 6);
  
endmodule
