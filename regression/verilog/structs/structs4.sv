module main;

  // The first field is the most-significant bit.
  struct packed {
    bit field1, field2;
    bit [6:0] field3;
  } s;

  initial begin
    s.field1 = 1;
    s.field2 = 0;
    s.field3 = 'b1110011;
  end

  // packed structs can be converted without cast to bit-vectors
  wire [8:0] w = s;

  // Expected to pass.
  p0: assert property (w == 'b1_0_1110011);

endmodule
