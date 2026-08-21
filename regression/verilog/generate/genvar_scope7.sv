module main;

  // The genvar declared in the header of the inner loop is local to that
  // loop, and hence shadows the genvar of the outer loop, 1800-2017 27.4.

  wire [3:0] some_wire;

  for (genvar i = 0; i < 2; i++)
  begin : a
    for (genvar i = 0; i < 2; i++)
    begin : b
      assign some_wire[i] = i == 1;
    end
  end

  always assert p1: some_wire[1:0] == 2'b10;

endmodule
