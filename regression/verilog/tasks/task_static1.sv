module top(input wire a, output reg y);

  task static copy;
    input x;
    output z;
    z = x;
  endtask

  always @* copy(a, y);

  p0: assert final (y == a);

endmodule
