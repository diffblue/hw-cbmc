module main;

  // The genvar declared in the header of the inner loop is local to that
  // loop, and hence shadows the genvar of the outer loop, 1800-2017 27.4.
  // Once the inner loop is done, the outer genvar is visible again.

  wire [3:0] some_wire;

  for (genvar i = 0; i < 2; i++)
  begin : a
    wire [1:0] w;
    for (genvar i = 0; i < 2; i++)
    begin : b
      assign w[i] = i == 1;
    end
    assign some_wire[i*2 +: 2] = w;
  end

  always assert p1: some_wire == 4'b1010;

endmodule
