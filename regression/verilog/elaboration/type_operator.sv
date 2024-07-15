module main;

  wire [31:0] some_wire;
  wire type(some_wire) other_wire;  

  parameter param0 = $bits(other_wire);

  p0: assert final (param0 == 32);

endmodule
