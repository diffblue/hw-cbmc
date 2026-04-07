module main;

  bit [0:3] array1;
  bit [3:0] array2;

  initial begin
    array1 = '{ 1, 1, 0, 1 };
    array2 = '{ 1, 1, 0, 1 };
  
    // Expected to pass.
    p11: assert (array1[0] == 1);
    p12: assert (array1[1] == 1);
    p13: assert (array1[2] == 0);
    p14: assert (array1[3] == 1);
    p15: assert (array1 == 4'b1101);

    p21: assert (array2[0] == 1);
    p22: assert (array2[1] == 0);
    p23: assert (array2[2] == 1);
    p24: assert (array2[3] == 1);
    p25: assert (array2 == 4'b1101);

  end

endmodule
