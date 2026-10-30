// The line number of a preprocessor error after a string literal that is
// continued on the next line (1800-2017 5.9).
module main;
  initial $display("a \
b");
`no_such_directive
endmodule
