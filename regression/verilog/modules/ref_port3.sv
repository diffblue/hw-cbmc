// A variable with an initial value, and one assigned through a ref port.
// The initial procedures run in an unspecified order (1800-2017 9.2.1),
// and the variable holds one of the values afterwards.
module writer(ref logic [3:0] y);
  initial y = 2;
endmodule

module main(input [3:0] x);
  logic [3:0] v;
  initial v = 1;
  writer w(v);

  p0: assert final (v == 1 || v == 2);

  // x is not constrained
  p1: assert final (x == 0);
endmodule
