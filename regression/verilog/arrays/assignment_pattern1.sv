module main;

  initial begin
    bit array1[3];
    bit [2:0] array2;
    bit [0:2] array3;

    array1 = '{ 1, 1, 0 };
    assert(array1[0]==1);
    assert(array1[1]==1);
    assert(array1[2]==0);

    array2 = '{ 1, 1, 0 };
    assert(array2[0]==0);
    assert(array2[1]==1);
    assert(array2[2]==1);

    array3 = '{ 1, 1, 0 };
    assert(array3[0]==1);
    assert(array3[1]==1);
    assert(array3[2]==0);
  end

endmodule
