module main;

  // 1800-2017 13.5.3: trailing arguments may be omitted when they have
  // a default value
  function automatic [7:0] f(input [7:0] a, input [7:0] b = 10, input [7:0] c = 20);
    f = a + b + c;
  endfunction

  p0: assert final (f(1) == 31);       // b and c default
  p1: assert final (f(1, 2) == 23);    // c defaults
  p2: assert final (f(1, 2, 3) == 6);  // all given, defaults overridden

endmodule
