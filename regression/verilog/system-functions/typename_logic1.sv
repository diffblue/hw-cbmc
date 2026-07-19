module main;

  logic some_bit;
  logic [31:0] vector1;
  logic [0:31] vector2;
  logic signed [31:0] vector3;

  // some simulators output 'reg' instead
  initial assert($typename(some_bit)=="logic");
  initial assert($typename(vector1)=="logic[31:0]");
  initial assert($typename(vector2)=="logic[0:31]");
  initial assert($typename(vector3)=="logic signed[31:0]");

endmodule
