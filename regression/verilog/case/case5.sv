module main;

  reg [31:0] resultA, resultB;

  // All case expressions are extended to the longest case
  // or case item expression.

  initial begin
    resultA = 10;

    case(1'b1 << 8)
      0: resultA = 0; // 32 bits!
      1'b1: resultA = 1;
    endcase

    assert(resultA == 10);
  end

  initial begin
    resultB = 10;

    case(1'b1 << 8)
      1'b0: resultB = 0; // just 1 bit!
      1'b1: resultB = 1;
    endcase

    assert(resultB == 0);
  end

endmodule
