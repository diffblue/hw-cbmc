// The newline after a one-line comment ending in a backslash
// still counts as a line.
module main;
  wire a; // comment ending in backslash \
  syntax error on line 5
endmodule
