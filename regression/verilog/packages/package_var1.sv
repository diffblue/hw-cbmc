package my_pkg;
  int my_var = 1;
endpackage

module main;
  import my_pkg::my_var;

  initial assert(my_var == 1);

endmodule
