module main;

  // An increasing range: w[0] is the most significant bit.
  wire [0:7] w = 8'hA5;

  p0: assert final (w[0] == 1);
  p1: assert final (w[0:3] == 4'hA);
  p2: assert final (w[4:7] == 4'h5);
  // w[2+:2] and w[3-:2] both select w[2:3]
  p3: assert final (w[2+:2] == 2'b10);
  p4: assert final (w[3-:2] == 2'b10);

endmodule
