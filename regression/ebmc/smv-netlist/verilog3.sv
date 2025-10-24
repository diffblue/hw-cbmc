module main;
  wire [7:0] some_wire;
  wire [31:0] something_else;
  assign something_else = some_wire[7:1];
endmodule
