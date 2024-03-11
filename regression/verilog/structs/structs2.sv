module main;

  // The first field is the most-significant bit.
  struct packed {
    bit field1, field2;
    bit [6:0] field3;
  } s;

  initial begin
    s.field1 = 1;
    s.field2 = 0;
    s.field3 = 127;
  end

  // Expected to pass.
  p1: assert property (s.field1 == 1);
  p2: assert property (s.field2 == 0);
  p3: assert property (s.field3 == 'b1111111);

endmodule
