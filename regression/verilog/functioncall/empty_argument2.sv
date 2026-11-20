module main;

  function [7:0] f(input [7:0] a, input [7:0] b);
    f = a + b;
  endfunction

  // 'a' has no default, so its position must not be empty;
  // this must not be read as f(5)
  wire [7:0] x = f(, 5);

endmodule
