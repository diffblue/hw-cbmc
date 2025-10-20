module main;

  // 1800-2017 6.24.1
  // "the cast shall return the value that a variable of the casting type
  // would hold after being assigned the expression."
  // Hence, this is an assignment context with $bits width.
  initial assert(signed'(1'b1 + 1'b1) == 0);

endmodule
