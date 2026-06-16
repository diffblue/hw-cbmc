module my_module#(parameter p0 = 0)();

  // 1800 2017 6.20.1
  // If the declaration of a design element uses a parameter_port_list (even
  // an empty one), then in any parameter_declaration directly contained
  // within the declaration, the parameter keyword shall be a synonym for
  // the localparam keyword
  localparam p1 = 1;
  parameter p2 = 2;

endmodule

module main;

  my_module #(10) my_instance();

  always assert p0: my_instance.p0==10;
  always assert p1: my_instance.p1==1;
  always assert p2: my_instance.p2==20;

endmodule
