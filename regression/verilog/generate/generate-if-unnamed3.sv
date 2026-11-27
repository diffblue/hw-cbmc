// Branches and loop bodies without begin-end are generate blocks, and
// hence scopes named genblk<n>, 1800-2017 27.5 and 27.6.
module buffer(input i, output o);
  assign o = i;
endmodule

module main(input [1:0] x);
  parameter P = 1;
  wire [1:0] y;

  // genblk1: a case generate construct
  generate
    case(P)
      0: logic [0:0] c;
      1: logic [1:0] c;
      default: logic [2:0] c;
    endcase
  endgenerate

  // genblk2: a loop that is the single item of a branch
  if(1) for(genvar i = 0; i < 2; i++) logic [3:0] d;

  // genblk3: a loop with an instance as its body
  generate
    for(genvar j = 0; j < 2; j++) buffer u(.i(x[j]), .o(y[j]));
  endgenerate

  // genblk4: a branch with an instance
  if(P == 1) buffer v(.i(x[0]), .o());

  p0: assert final ($bits(genblk1.c) == 2);
  p1: assert final ($bits(genblk2.genblk1[1].d) == 4);
  p2: assert final (y == x);
  p3: assert final (genblk3[1].u.o == x[1]);
  p4: assert final (genblk4.v.i == x[0]);
endmodule
