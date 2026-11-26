// Triple-quoted string literals (IEEE 1800-2023 5.9)
module main;

  // a newline in the literal is a newline in the string
  p0: assert final ("""a
b""" == "a\nb");

  // an unescaped double quote
  p1: assert final ("""x"y""" == "x\"y");

  // two consecutive double quotes
  p2: assert final ("""x""y""" == "x\"\"y");

  // escape sequences work as in other string literals
  p3: assert final ("""a\tb""" == "a\tb");

endmodule
