module main(input [1:0] x);

  // An explicitly declared name that is the name that 1800-2017 27.6 would
  // give to the block of the loop below. Leading zeros are then added to
  // the number of the loop, giving genblk01.
  wire genblk1 = x[0];

  genvar g;

  for(g = 0; g < 2; g = g + 1) begin
    wire t = x[g];
  end

  p0: assert final (genblk01[1].t == x[1]);
  p1: assert final (genblk1 == x[0]);

endmodule
