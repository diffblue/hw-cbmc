// $clog2 of a non-constant value.
module main(input [3:0] a);
  bit b;
  always_comb if($clog2(a) == 3) b = 1; else b = 0;
endmodule
