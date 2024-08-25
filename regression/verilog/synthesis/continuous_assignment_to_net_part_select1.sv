module main;

  wire [31:0] some_wire;
  assign some_wire[1:0] = 'b01;

  p0: assert final (some_wire[1:0] == 1);

endmodule
