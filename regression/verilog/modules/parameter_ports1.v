module my_zero_tester
#(parameter WIDTH = 32)
(input [WIDTH-1:0] i, output is_zero);

  assign is_zero = i == 0;

endmodule // my_zero_tester

module main;

  wire [7:0] data = 123;
  my_zero_tester t(data, zero);

  always assert p1: !zero;

endmodule // main
