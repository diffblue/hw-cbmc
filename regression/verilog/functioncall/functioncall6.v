module main;

  function [7:0] a_constant;
    a_constant = 123;
  endfunction

  wire [7:0] w = a_constant();

  always assert p1: w == 123;

endmodule
