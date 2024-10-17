module main;

  bit some_bit;
  bit [31:0] vector1;
  bit [0:31] vector2;
  bit signed [31:0] vector3;

  assert final ($typename(some_bit)=="bit");
  assert final ($typename(vector1)=="bit[31:0]");
  assert final ($typename(vector2)=="bit[0:31]");
  assert final ($typename(vector3)=="bit signed[31:0]");

  // $typename yields an elaboration-time constant
  parameter P = $typename(some_bit);

endmodule
