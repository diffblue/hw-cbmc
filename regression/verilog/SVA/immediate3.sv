module full_adder(input a, b, c, output sum, carry);

  assign sum = a ^ b ^ c;
  assign carry = a & b | (a ^ b) & c;

  always @(*)
    assert final({carry, sum} == {1'b0, a} + b + c);

endmodule
