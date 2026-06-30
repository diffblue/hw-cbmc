package my_pkg;
  property is_true;
    1
  endproperty
endpackage

module main;
  // holds
  assert property (my_pkg::is_true);
endmodule
