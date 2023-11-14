module my_module#(p0 = 0)();

  localparam p1 = 1;
  parameter p2 = 2;

endmodule

module main;

  my_module #(10, 20) instance();

  always assert p0: instance.p0==10;
  always assert p1: instance.p1==1;
  always assert p2: instance.p2==20;

endmodule
