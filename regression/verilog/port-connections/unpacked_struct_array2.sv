// An output port of an unpacked array type is connected to an unpacked
// array with a different number of elements, which is an error.
module child(input clk, output logic [21:0] o [0:1]);
endmodule

module main(input clk);
  logic [21:0] x [0:2];
  child c(.clk(clk), .o(x));
endmodule
