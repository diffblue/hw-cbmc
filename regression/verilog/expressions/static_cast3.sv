module main;

  typedef bit [7:0] eight_bits;

  // 1800-2017 6.24.1
  // "the cast shall return the value that a variable of the casting type
  // would hold after being assigned the expression."
  // Hence, this is an assignment context.
  initial assert(eight_bits'(1'b1 + 1'b1) == 8'd2);

endmodule
