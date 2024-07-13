module full_adder(input a, b, c, output sum, carry);

  assign sum = a ^ b ^ c;
  assign carry = a & b | (a ^ b) & c;

  always @(*)
    assert final({carry, sum} == a + b + c);

endmodule
