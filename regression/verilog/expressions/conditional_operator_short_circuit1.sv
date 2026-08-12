module main;

  // Per 1800-2017 11.4.11, the conditional operator evaluates the first
  // expression when the condition is true, and the second expression when
  // it is false.  Only when the condition is ambiguous are both operands
  // evaluated.  The condition here is 0, hence 1/0 is not evaluated and the
  // range is [2:0].
  wire [(0 ? 1/0 : 3)-1:0] x;

  initial assert ($bits(x) == 3);

endmodule
