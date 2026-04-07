module main;

  typedef bit my_bit;
  my_bit [7:0] my_vector;

  initial p0: assert($bits(my_vector) == 8);

endmodule
