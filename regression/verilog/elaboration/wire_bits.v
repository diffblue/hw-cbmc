module main;

  wire [31:0] some_wire;
  wire [$bits(some_wire)-1:0] other_wire;  
  supply0 [$bits(some_wire)-1:0] some_supply0;
  supply1 [$bits(some_wire)-1:0] some_supply1;
  parameter param0 = $bits(some_supply0);
  parameter param1 = $bits(some_supply1);

  always assert p0: param0 == 32;
  always assert p1: param1 == 32;

endmodule
