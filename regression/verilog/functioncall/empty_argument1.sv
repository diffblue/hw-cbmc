module main;

  function [7:0] f(input [7:0] a = 1, input [7:0] b = 2, input [7:0] c = 3);
    f = a * 100 + b * 10 + c;
  endfunction

  // 1800-2017 13.5.3: an empty position in the argument list
  // uses the default value of the corresponding formal
  p0: assert final (f(, 5, 6) == 156);
  p1: assert final (f(4, , 6) == 426);
  p2: assert final (f(4, 5, ) == 453);
  p3: assert final (f(, , ) == 123);
  p4: assert final (f(, .c(9)) == 129);

endmodule
