module main;

  struct packed {
    bit field1, field2;
    bit [6:0] field3;
  } s = '{ 1, 0, 'b1110011 };

  // Expected to pass.
  p1: assert property (s.field1 == 1);
  p2: assert property (s.field2 == 0);
  p3: assert property (s.field3 == 'b1110011);

endmodule
