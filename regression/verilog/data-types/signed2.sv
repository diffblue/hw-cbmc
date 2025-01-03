module main;

  assert final ($typename(bit) == "bit");
  assert final ($typename(bit unsigned) == "bit");
  assert final ($typename(bit unsigned[1:0]) == "bit[1:0]");
  assert final ($typename(bit signed) == "bit signed[0:0]");
  assert final ($typename(bit signed[1:0]) == "bit signed[1:0]");
  assert final ($typename(byte) == "bit signed[7:0]");
  assert final ($typename(byte unsigned) == "bit[7:0]");
  assert final ($typename(byte signed) == "bit signed[7:0]");
  assert final ($typename(int) == "bit signed[31:0]");
  assert final ($typename(int unsigned) == "bit[31:0]");
  assert final ($typename(int signed) == "bit signed[31:0]");
  assert final ($typename(integer) == "bit signed[31:0]");
  assert final ($typename(integer unsigned) == "bit[31:0]");
  assert final ($typename(integer signed) == "bit signed[31:0]");

endmodule
