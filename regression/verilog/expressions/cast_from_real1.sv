module main;

  always assert (integer'(1.0) == 1);
  always assert (integer'(-1.0) == -1);

  // Casting rounds away from zero (1800-2017 6.12.2)
  always assert (integer'(1.9) == 2);

endmodule
