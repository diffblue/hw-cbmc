module my_module;

  parameter some_parameter = 8;

  // typedefs may depend on parameters  
  typedef bit [some_parameter-1:0] some_type;
  wire some_type some_wire = -1;

endmodule

module main;

  my_module m8();
  my_module #(.some_parameter(4)) m4();
  my_module #(2) m2();

  initial p1: assert (m8.some_wire==255);
  initial p2: assert (m4.some_wire==15);
  initial p3: assert (m2.some_wire==3);

endmodule
