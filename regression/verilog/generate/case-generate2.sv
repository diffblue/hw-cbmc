module main;

  parameter P = 10;

  reg [7:0] out;

  generate
    case (P)
      0: assign out = 8'h00;
      1: assign out = 8'hff;
      default: assign out = 8'h42;
    endcase
  endgenerate

  always assert p1: out == 8'h42;

endmodule
