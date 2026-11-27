module main(input [1:0] x);

  parameter P = 2;

  // 1800-2017 27.5 and 27.6: the unnamed blocks of a conditional generate
  // construct are scopes named genblk<n>, where n is the number of the
  // construct in the module. An else-if chain without begin-end is one
  // construct.
  if(P == 1) begin
    wire w = x[0];
  end
  else if(P == 2) begin
    wire w = x[1];
  end

  // the second generate construct
  for(genvar g = 0; g < 2; g++) begin
    wire v = x[g];
  end

  p0: assert final (genblk1.w == x[1]);
  p1: assert final (genblk2[0].v == x[0]);

endmodule
