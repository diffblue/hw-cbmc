package my_pkg;
  int my_var;
endpackage

module main;
  import my_pkg::my_var;

  initial my_var = 42;

  p0: assert property (my_var == 42);
endmodule
