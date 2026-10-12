// Width behaviour for an implicit net declared as a concatenation member on
// the LHS of a continuous assignment (IEEE 1800-2017 6.10, 11.4.1 / 11.6).
// `carry` is undeclared and becomes a scalar (1-bit) net. The LHS {carry, out}
// is therefore 5 bits wide and establishes the context size of the
// right-hand side, so a + b is evaluated at 5 bits and `carry` receives the
// genuine carry-out of the addition rather than being truncated. There is no
// lhs/rhs width-mismatch error; the RHS is extended to the LHS width.
module main(input [3:0] a, input [3:0] b, output [3:0] out);

  assign {carry, out} = a + b;

  // 4'hF + 4'h1 = 5'b1_0000 -> carry == 1, out == 0
  always assert final (!(a == 4'hF && b == 4'h1) || (carry == 1 && out == 0));

endmodule
