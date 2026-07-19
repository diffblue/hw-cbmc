module main;

  reg some_bit;
  reg [31:0] vector1;
  reg [0:31] vector2;
  reg signed [31:0] vector3;

  // some simulators output 'logic' instead
  initial assert($typename(some_bit)=="reg");
  initial assert($typename(vector1)=="reg[31:0]");
  initial assert($typename(vector2)=="reg[0:31]");
  initial assert($typename(vector3)=="reg signed[31:0]");

endmodule
