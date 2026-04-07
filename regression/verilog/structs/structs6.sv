module main;

  struct packed {
    bit field1, field2;
    bit [6:0] field3;
  } s = '{ 1'b1, 1'b0, 7'b1110010 };

  // Extract some bits from the struct.
  // Expected to pass.
  p1: assert property(s[-1] == 0);
  p2: assert property(s[6:0] == 'b1110010); // field3
  p3: assert property(s[7] == 1'b0); // field2
  p4: assert property(s[8] == 1'b1); // field1

endmodule
