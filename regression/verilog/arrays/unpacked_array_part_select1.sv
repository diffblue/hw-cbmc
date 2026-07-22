module main;

  int array1[4];
  int array2[2];

  // 1800-2017 7.4.3: reading and writing a slice of the array is
  // supported for unpacked arrays. ebmc does not yet implement this,
  // and rejects the part-select (slicing) operator on unpacked arrays
  // during type-checking.
  initial begin
    array1 = '{ 0, 1, 2, 3 };

    // read a slice
    array2 = array1[0:1];
    assert(array2[0] == 0 && array2[1] == 1);

    // write a slice
    array1[2:3] = array2;
    assert(array1[2] == 0 && array1[3] == 1);
  end

endmodule
