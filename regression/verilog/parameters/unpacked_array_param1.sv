// Unpacked array dimensions on a parameter/localparam declarator,
// e.g. "parameter logic [3:0] p [3] = '{...}" (IEEE 1800-2017 A.2.4).
// Reduced from LogikBench blocks/spi and large/cva6.
module main;
  parameter  logic [3:0] PERMIT [3]   = '{4'b0001, 4'b0010, 4'b0100};
  localparam logic [7:0] Masks  [2:4] = '{8'hC, 8'h1E, 8'h39};
  wire [3:0] x = PERMIT[1];
  wire [7:0] y = Masks[3];
endmodule
