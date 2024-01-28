module main;

  wire [31:0] some_wire;
  wire type(some_wire) other_wire;

  typedef bit [31:0] some_type;
  wire some_type next_wire;

  p0: assert property ($bits(other_wire) == 32);
  p1: assert property ($bits(next_wire) == 32);

endmodule
