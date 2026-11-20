// A system function applied to a variable whose value is not known
// in an initial block.
module main;
  bit [3:0] a;
  int b;

  initial b = $countones(a);

  p0: assert final (b <= 4);
endmodule
