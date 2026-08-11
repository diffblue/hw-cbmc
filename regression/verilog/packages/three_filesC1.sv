module top;

  import other_pkg::*;

  other_type some_var;

  initial assert($bits(some_var) == 8);

endmodule
