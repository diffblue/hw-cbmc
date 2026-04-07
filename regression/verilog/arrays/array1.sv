module main;

  reg [7:0] my_array0[10];
  reg [7:0] my_array1[9:0];
  reg [7:0] my_array2[4:-5];
  reg [7:0] my_array3[0:9];
  reg [7:0] my_array4[-10:-1];

  // Icarus Verilog says 8, but that's wrong.
  initial begin
    p0: assert ($bits(my_array0) == 8*10);
    p1: assert ($bits(my_array1) == 8*10);
    p2: assert ($bits(my_array2) == 8*10);
    p3: assert ($bits(my_array3) == 8*10);
    p4: assert ($bits(my_array4) == 8*10);
  end

endmodule
