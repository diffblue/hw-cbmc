package my_pkg;
  int x;
endpackage

import my_pkg::*;

// non-ANSI syntax
module main(x);
  input x;

  // should pass, it's not my_pkg::x
  initial assert($bits(x) == 1);

endmodule
