module main;

  reg [7:0] my_array0[10];
  reg [7:0] my_array1[9:0];
  reg [7:0] my_array2[4:-5];
  reg [7:0] my_array3[0:9];
  reg [7:0] my_array4[-10:-1];

  // Icarus Verilog says 8, but that's wrong.
  always assert p0: ($bits(my_array0) == 8*10);
  always assert p1: ($bits(my_array1) == 8*10);
  always assert p2: ($bits(my_array2) == 8*10);
  always assert p3: ($bits(my_array3) == 8*10);
  always assert p4: ($bits(my_array4) == 8*10);

endmodule
