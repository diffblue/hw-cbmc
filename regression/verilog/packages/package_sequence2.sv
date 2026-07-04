package my_pkg;
  int x;

  sequence x_is_ten;
    x == 10
  endsequence
endpackage

module main;
  // will be covered
  cover sequence (my_pkg::x_is_ten);
endmodule
