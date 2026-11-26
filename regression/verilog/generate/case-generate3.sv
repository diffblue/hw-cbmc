// A case generate construct that is a module item, outside of a generate
// region, 1800-2017 27.5.
module sub(input [7:0] i, output [7:0] o);
  assign o = i;
endmodule

module main;

  parameter P = 1;

  wire [7:0] out;

  case (P)
    0: assign out = 8'h00;
    1: sub s(.i(8'hff), .o(out));
    default: assign out = 8'h42;
  endcase

  p1: assert final (out == 8'hff);

endmodule
