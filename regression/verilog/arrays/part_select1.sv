module main;

  int array1[4];
  int array2[3:0];
  int array3[0:3];

  typedef int twoarr[1:0];
  
  initial begin
    array1 = '{ 0, 1, 2, 3 };
    assert(array1[0:1] == twoarr'{ 0, 1 });
    assert(array1[2:3] == twoarr'{ 2, 3 });

    array2 = '{ 0, 1, 2, 3 };
    assert(array2[1:0] == twoarr'{ 2, 3 });
    assert(array2[3:2] == twoarr'{ 0, 1 });

    array3 = '{ 0, 1, 2, 3 };
    assert(array3[0:1] == twoarr'{ 0, 1 });
    assert(array3[2:3] == twoarr'{ 2, 3 });
  end

endmodule
