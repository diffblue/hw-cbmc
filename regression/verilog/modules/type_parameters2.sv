module main;

  parameter type T1 = bit [31:0];

  T1 some_data;

  initial assert ($bits(some_data) == 32);

endmodule
