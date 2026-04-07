package my_pkg;
  int my_var;
endpackage

module main;
  import my_pkg::my_var;

  initial assert($bits(my_var) == 32);

endmodule
