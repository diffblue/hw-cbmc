module main;

  wire some_bit;
  wire [31:0] vector1;
  wire [0:31] vector2;
  wire signed [31:0] vector3;

  // some simulators output 'logic' instead
  initial assert($typename(some_bit)=="wire");
  initial assert($typename(vector1)=="wire[31:0]");
  initial assert($typename(vector2)=="wire[0:31]");
  initial assert($typename(vector3)=="wire signed[31:0]");

endmodule
