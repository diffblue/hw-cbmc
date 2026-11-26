module main;
  p0: assert final ("""a
b""" == "a\nb");
  // the line number of an error after a multiline literal is correct
  foo bar;
endmodule
