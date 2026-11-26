module main(input signed [3:0] a, b, c, d);

  // Slices of a wire, defined by products of signed operands, which
  // are cast to the unsigned type of the slice
  wire [15:0] out;
  assign out[7:0] = a * b;
  assign out[15:8] = c * d;

  // the same products, from the operands sign-extended to 8 bits
  p0: assert final (out[7:0] == {{4{a[3]}}, a} * {{4{b[3]}}, b});
  p1: assert final (out[15:8] == {{4{c[3]}}, c} * {{4{d[3]}}, d});

endmodule
