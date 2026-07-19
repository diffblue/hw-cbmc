module main;

  bit some_bit;
  bit [31:0] vector1;
  bit [0:31] vector2;
  bit signed [31:0] vector3;

  initial assert($typename(some_bit)=="bit");
  initial assert($typename(vector1)=="bit[31:0]");
  initial assert($typename(vector2)=="bit[0:31]");
  initial assert($typename(vector3)=="bit signed[31:0]");

  // $typename yields an elaboration-time constant
  parameter P = $typename(some_bit);

endmodule
