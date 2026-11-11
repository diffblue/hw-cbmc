// 1800-2017 22.5.1: a one-line comment ending in a backslash continues
// only a `define; elsewhere the backslash is part of the comment.
module main;
  wire a = 1; // comment ending in backslash \
  wire b = a;
  p0: assert final (b);
endmodule
