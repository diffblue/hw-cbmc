module my_zero_tester
#(parameter WIDTH = 32, parameter P2 = 10, P3 = 20)
(input [WIDTH-1:0] i, output is_zero);

  assign is_zero = i == 0;

endmodule // my_zero_tester

module main;

  wire [7:0] data = 123;
  wire is_zero;
  my_zero_tester #(8) t(data, is_zero);

  always assert p1: !is_zero;

endmodule // main
