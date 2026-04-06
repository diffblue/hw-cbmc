package my_pkg;
  wire [31:0] my_net;
endpackage

module main;
  import my_pkg::my_net;
  initial assert($bits(my_net) == 32);
endmodule
