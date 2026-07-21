module main;

  bit some_array['h10];
  bit other_array[2:20];
  bit next_array[20:2];
  bit multi_array[3:0][7:0];
  int array_of_int[3];
  bit [7:0][5:0][3:0] packed3d;
  bit [7:0][5:0][3:0] packed3d_unpacked1d [0:4];

  // Array sizes must be unsigned decimal; the declarator is turned into '$'
  initial assert($typename(some_array)=="bit$[0:15]");
  initial assert($typename(other_array)=="bit$[2:20]");
  initial assert($typename(next_array)=="bit$[20:2]");
  initial assert($typename(multi_array)=="bit$[3:0][7:0]");
  initial assert($typename(array_of_int)=="int$[0:2]");
  initial assert($typename(packed3d)=="bit[7:0][5:0][3:0]");
  initial assert($typename(packed3d_unpacked1d)=="bit[7:0][5:0][3:0]$[0:4]");

endmodule
