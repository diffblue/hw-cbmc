module main;

  bit [1:4] [7:0] array1;
  bit [4:1] [7:0] array2;

  initial begin
    array1 = '{ 1, 2, 3, 4 };
    array2 = '{ 1, 2, 3, 4 };
  
    // Expected to pass.
    p11: assert (array1[1] == 1);
    p12: assert (array1[2] == 2);
    p13: assert (array1[3] == 3);
    p14: assert (array1[4] == 4);
    p15: assert (array1 == 32'h01020304);

    p21: assert (array2[1] == 4);
    p22: assert (array2[2] == 3);
    p23: assert (array2[3] == 2);
    p24: assert (array2[4] == 1);
    p25: assert (array2 == 32'h01020304);

  end

endmodule
