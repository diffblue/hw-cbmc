// Ports may use SystemVerilog datatypes.
module main(input logic [31:0] data);

  always assert final1: $bits(data) == 32;

endmodule
