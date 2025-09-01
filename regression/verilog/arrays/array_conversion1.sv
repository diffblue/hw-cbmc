module main;

  // that's 4 bytes, packed
  wire [3:0][7:0] my_bytes = '{ 1, 2, 3, 4 };

  // can be converted implicitly
  wire [63:0] my_word = my_bytes;

  assert final(my_word == 64'h04030201);

endmodule
