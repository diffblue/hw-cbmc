package my_pkg;
  int x;

  property x_is_ten;
    x == 10
  endproperty
endpackage

module main;
  // fails
  assert property (my_pkg::x_is_ten);
endmodule
