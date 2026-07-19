module main;

  bit some_array['h10];
  bit other_array[2:20];
  bit next_array[20:2];

  // Array sizes must be unsigned decimal; the declarator is turned into '$'
  initial assert($typename(some_array)=="bit$[0:15]");
  initial assert($typename(other_array)=="bit$[2:20]");
  initial assert($typename(next_array)=="bit$[20:2]");

endmodule
