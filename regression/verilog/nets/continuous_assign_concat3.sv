// The implicit-net rule for undeclared identifiers on a continuous-assign LHS
// (IEEE 1800-2017 6.10) also applies when the identifier is nested inside an
// inner concatenation, e.g. {{carry}, out}. `carry` is undeclared and becomes
// a scalar net; descent into the nested concatenation must find it. The 5-bit
// LHS context widens the addition, so carry receives the real carry-out.
module main(input [3:0] a, input [3:0] b, output [3:0] out);

  assign {{carry}, out} = a + b;

  // 4'hF + 4'h1 = 5'b1_0000 -> carry == 1, out == 0
  always assert final (!(a == 4'hF && b == 4'h1) || (carry == 1 && out == 0));

endmodule
