module main;

  typedef bit unsigned [7:0] unsigned_eight_bits;
  typedef bit signed [7:0] signed_eight_bits;

  // 1800-2017 6.24.1
  // "the cast shall return the value that a variable of the casting type
  // would hold after being assigned the expression."
  // Hence, this is an assignment context.
  initial assert(unsigned_eight_bits'(1'b1 + 1'b1) == 8'd2);
  initial assert(unsigned_eight_bits'(1'sb1 + 1'sb1) == 8'b11111110);
  initial assert(signed_eight_bits'(1'b1 + 1'b1) == 8'd2);
  initial assert(signed_eight_bits'(1'sb1 + 1'sb1) == 8'sb11111110);

endmodule
