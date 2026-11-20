package pkg;
  parameter P = 7;

  function automatic [7:0] f(input [7:0] a = P);
    f = a;
  endfunction
endpackage

module main;

  parameter Q = 5;

  // The default is evaluated in the scope of the declaration
  // (1800-2017 13.5.3); the parameter P of the module is not used.
  parameter P = 3;

  function automatic [7:0] g(input [7:0] a = Q + 1);
    g = a;
  endfunction

  p0: assert final (pkg::f() == 7);
  p1: assert final (g() == 6);

endmodule
