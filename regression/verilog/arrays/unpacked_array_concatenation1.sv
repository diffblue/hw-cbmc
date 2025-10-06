module main;

  // 1800-2017 10.10 Unpacked array concatenation
  byte my_bytes [1:4] = { 1, 2, 3, 4 };

  assert final(my_bytes[1] == 1);
  assert final(my_bytes[2] == 2);
  assert final(my_bytes[3] == 3);
  assert final(my_bytes[4] == 4);

endmodule
