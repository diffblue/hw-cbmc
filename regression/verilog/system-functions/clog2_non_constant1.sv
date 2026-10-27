// $clog2 of a non-constant value; 1800-2017 20.8.1 does not require
// the argument to be constant.
module main(input [3:0] a);
  bit b;
  always_comb if($clog2(a) == 3) b = 1; else b = 0;
  p0: assert final (a == 5 -> b == 1);
  p1: assert final (a == 4 -> b == 0);
endmodule
