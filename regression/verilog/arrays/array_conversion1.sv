module main;

  // that's 4 bytes, packed
  wire [3:0][7:0] my_bytes = '{ 1, 2, 3, 4 };

  // can be converted implicitly
  wire [63:0] my_word = my_bytes;

  assert final(my_word == 64'h01020304);

  // works with unary minus
  assert final(-my_bytes == -64'h01020304);

  // works with unary plus
  assert final(+my_bytes == 64'h01020304);

  // works with power
  assert final(my_bytes**1 == 64'h01020304);

  // works with arithmetic operators
  assert final(my_bytes+1 == 64'h01020305);

  // works with relational operators
  assert final(my_bytes < 64'h01020305);

endmodule
