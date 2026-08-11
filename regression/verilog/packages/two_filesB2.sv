import my_package::*;

module top;
  some_type some_var;
  initial assert($bits(some_var) == 32);
endmodule
