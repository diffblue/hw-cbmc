module main;

  typedef bit my_bit;
  my_bit [7:0] my_vector;

  always assert p0: ($bits(my_vector) == 8);

endmodule
