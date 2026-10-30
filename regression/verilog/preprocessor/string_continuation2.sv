// Line numbers after string literals that are continued on the next line
// (1800-2017 5.9): in code, in a macro argument, and in macro text. The
// preprocessor's line numbers are checked with `__LINE__, the parser's
// with the line numbers of the "Making ... a wire" messages.
`define m(a, b) a
module main;
  logic l1 = 0;
  initial $display("a \
b");
  p0: assert final (`__LINE__ == 10);
  logic l2 = 0;
  initial $display(`m("c \
d,e", 1));
  p1: assert final (`__LINE__ == 14);
  logic l3 = 0;
`define s "g \
h"
  initial $display(`s);
  p2: assert final (`__LINE__ == 19);
  logic l4 = 0;
  assign l1 = 1, l2 = 1, l3 = 1, l4 = 1;
endmodule
