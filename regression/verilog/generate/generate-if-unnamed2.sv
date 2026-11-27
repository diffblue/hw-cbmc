// The example of 1800-2017 27.6, with distinct widths to tell the
// declarations apart. The generate blocks without begin-end are scopes
// as well, 1800-2017 27.5.
module main;
  parameter genblk2 = 0;
  genvar i;

  // genblk1
  if(genblk2) logic [0:0] a;
  else logic [1:0] b;

  // genblk02, since genblk2 is declared
  if(genblk2) logic [2:0] a;
  else logic [3:0] b;

  // the third construct, named g1
  for(i = 0; i < 1; i = i + 1) begin : g1
    // genblk1, the first construct in g1
    if(1) logic [4:0] a;
  end

  // genblk4, the fourth construct
  for(i = 0; i < 1; i = i + 1)
    // genblk1, the first construct in genblk4[0]
    if(1) logic [5:0] a;

  // genblk5, an else-if chain without begin-end is one construct
  if(0) logic [6:0] a;
  else if(1) logic [7:0] a;

  p0: assert final ($bits(genblk1.b) == 2);
  p1: assert final ($bits(genblk02.b) == 4);
  p2: assert final ($bits(g1[0].genblk1.a) == 5);
  p3: assert final ($bits(genblk4[0].genblk1.a) == 6);
  p4: assert final ($bits(genblk5.a) == 8);
endmodule
