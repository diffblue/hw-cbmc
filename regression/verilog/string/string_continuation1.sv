// A backslash followed by a newline in a string literal is a line
// continuation; neither is part of the string (IEEE 1800-2017 5.9).
module main;
  p0: assert final ("a \
b" == "a b");
  p1: assert final ("a \
b" != "a \nb");
endmodule
