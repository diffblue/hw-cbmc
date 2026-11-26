// Triple-quoted string literals (IEEE 1800-2023 5.9)
module main;

  // a newline in the literal is a newline in the string
  localparam string s1 = """a
b""";

  // an unescaped double quote
  localparam string s2 = """x"y""";

  p0: assert final (s1 == "a\nb");
  p1: assert final (s2 == "x\"y");

endmodule
