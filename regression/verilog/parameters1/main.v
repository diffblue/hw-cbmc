module my_module;

  parameter some_parameter = 7;
  
  wire [some_parameter:0] some_wire = -1;

endmodule

module main;

  my_module m1();
  my_module #(.some_parameter(3)) m2();
  my_module #(1) m3();

  always assert p1: m1.some_wire==255;
  always assert p2: m2.some_wire==15;
  always assert p3: m3.some_wire==3;

endmodule
