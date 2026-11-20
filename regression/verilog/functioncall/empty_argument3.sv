module main;

  function [7:0] g(input [7:0] a);
    g = a;
  endfunction

  // Two positions for one formal; this must not be read as g(5)
  p0: assert final (g(, 5) == 5);

endmodule
