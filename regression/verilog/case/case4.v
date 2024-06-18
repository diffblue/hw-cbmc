module m(input [7:0] i, output reg [31:0] x);

  always @(*)
    casex(i)
      8'b1x: x=1;
      8'bxx: x=2;
      8'b11xx: x=3;
      default: x=4;
    endcase

endmodule

module main();

  wire [7:0] i, x;

  m m(i, x);

  always assert p1:
    x==
    ((i&'b1111_1110)=='b0000_0010)?1:
    ((i&'b1111_1100)=='b0000_0000)?2:
    ((i&'b1111_1100)=='b0000_1100)?3:4;

endmodule
