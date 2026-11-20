module main;

  function automatic [7:0] f(input [7:0] a, input [7:0] b = 10);
    f = a + b;
  endfunction

  // a has no default value
  p0: assert final (f() == 10);

endmodule
