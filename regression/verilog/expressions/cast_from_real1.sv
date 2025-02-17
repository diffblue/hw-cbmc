module main;

  always assert (integer'(1.0) == 1);
  always assert (integer'(-1.0) == -1);

  // Casting rounds to nearest-ties-away-from zero (1800-2017 6.12.2)
  // Examples from the standard.
  always assert (integer'(35.7) == 36);
  always assert (integer'(35.5) == 36);
  always assert (integer'(35.2) == 35);
  always assert (integer'(-1.5) == -2);
  always assert (integer'(1.5) == 2);

endmodule
