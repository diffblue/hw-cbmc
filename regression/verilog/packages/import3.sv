package my_pkg;
  typedef int my_type;
endpackage

module main;
  import my_pkg::my_type;
  assert final($typename(my_type) == "int");
endmodule
