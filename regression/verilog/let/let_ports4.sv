// let with ports, with default values and typed formals, 1800-2017 11.12

module main(input [7:0] x);

  let f(a, b = 2, c = 3) = a + b + c;
  let g(logic [3:0] a) = a;
  let h(untyped a = 7) = a;

  p0: assert final (f(1) == 6);
  p1: assert final (f(1, 5) == 9);
  p2: assert final (f(.a(1), .c(10)) == 13);
  p3: assert final (f(1, .c()) == 6);

  // typed formals cast the actual argument
  p4: assert final (g(8'hff) == 15);
  p5: assert final ($bits(g(x)) == 4);

  // no parentheses
  p6: assert final (h == 7);
  p7: assert final (h() == 7);

endmodule
