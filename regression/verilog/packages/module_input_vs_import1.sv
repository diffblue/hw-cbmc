package my_pkg;
  int x;
endpackage

import my_pkg::*;

// ANSI syntax
module main(input x);

  // should pass, it's not my_pkg::x
  initial assert($bits(x) == 1);

endmodule
