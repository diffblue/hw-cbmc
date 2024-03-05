module main(input x, input y);

  reg result;

  always @(x, y)
    case(x)
      0: result = 0;
      1:
        case(y)
          1: result = 1;
          0: result = 0;
        endcase
    endcase

  always assert p1: result == (x && y);

endmodule
