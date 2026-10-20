module main;

  // IEEE 1800-2017 11.4.4: the relational operators yield x
  // if either operand contains x or z bits.

  initial assert ((4'b0011 < 4'b0100) === 1'b1);
  initial assert ((4'b0100 < 4'b0011) === 1'b0);
  initial assert ((4'b00x1 < 4'b0100) === 1'bx);

  initial assert ((4'b0011 <= 4'b0011) === 1'b1);
  initial assert ((4'b0100 <= 4'b0011) === 1'b0);
  initial assert ((4'b0011 <= 4'b01z0) === 1'bx);

  initial assert ((4'b0100 > 4'b0011) === 1'b1);
  initial assert ((4'b0011 > 4'b0100) === 1'b0);
  initial assert ((4'b00x1 > 4'b0100) === 1'bx);

  initial assert ((4'b0011 >= 4'b0011) === 1'b1);
  initial assert ((4'b0011 >= 4'b0100) === 1'b0);
  initial assert ((4'b0011 >= 4'b01z0) === 1'bx);

  // the same in a constant expression
  parameter logic P_gt = 4'b00x1 > 4'b0100;
  parameter logic P_lt = 4'b00x1 < 4'b0100;
  initial assert (P_gt === 1'bx);
  initial assert (P_lt === 1'bx);

endmodule
