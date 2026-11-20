module main;

  function automatic [7:0] f(input [7:0] a = 1, input [7:0] b, input [7:0] c = 3);
    f = 100 * a + 10 * b + c;
  endfunction

  // 1800-2017 13.5.4: named arguments combined with defaults
  p0: assert final (f(.b(2)) == 123);
  p1: assert final (f(.c(5), .b(2)) == 125);
  p2: assert final (f(2, .b(0)) == 203);
  // an empty named argument uses the default
  p3: assert final (f(.a(), .b(4), .c()) == 143);

endmodule
