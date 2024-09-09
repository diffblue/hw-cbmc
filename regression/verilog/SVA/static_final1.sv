module full_adder(input a, b, c, output sum, carry);

  assign sum = a ^ b ^ c;
  assign carry = a & b | (a ^ b) & c;

  // 1800-2017
  // 16.4.3 Deferred assertions outside procedural code
  p0: assert final ({carry, sum} == {1'b0, a} + b + c);

endmodule
