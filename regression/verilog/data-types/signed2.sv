module main;

  assert final ($typename(bit) == "bit");
  assert final ($typename(bit unsigned) == "bit");
  assert final ($typename(bit unsigned[1:0]) == "bit[1:0]");
  assert final ($typename(bit signed) == "bit signed[0:0]");
  assert final ($typename(bit signed[1:0]) == "bit signed[1:0]");
  assert final ($typename(byte) == "byte");
  assert final ($typename(byte unsigned) == "byte unsigned");
  assert final ($typename(byte signed) == "byte");
  assert final ($typename(int) == "int");
  assert final ($typename(int unsigned) == "int unsigned");
  assert final ($typename(int signed) == "int");
  assert final ($typename(shortint) == "shortint");
  assert final ($typename(shortint unsigned) == "shortint unsigned");
  assert final ($typename(shortint signed) == "shortint");
  assert final ($typename(longint) == "longint");
  assert final ($typename(longint unsigned) == "longint unsigned");
  assert final ($typename(longint signed) == "longint");
  assert final ($typename(integer) == "bit signed[31:0]");
  assert final ($typename(integer unsigned) == "bit[31:0]");
  assert final ($typename(integer signed) == "bit signed[31:0]");

endmodule
