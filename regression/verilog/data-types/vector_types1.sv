module main;

  var [7:0] implicit;
  var bit [7:0] some_bits;
  var logic [7:0] some_logic;
  var unsigned [7:0] implicit_unsigned;
  var bit unsigned [7:0] some_bits_unsigned;
  var logic unsigned [7:0] some_logic_unsigned;
  var signed [7:0] implicit_signed;
  var bit signed [7:0] some_bits_signed;
  var logic signed [7:0] some_logic_signed;

  // expected to pass
  p0: assert final ($bits(implicit) == 8);
  p1: assert final ($bits(some_bits) == 8);
  p2: assert final ($bits(some_logic) == 8);
  p3: assert final ($bits(implicit_unsigned) == 8);
  p4: assert final ($bits(some_bits_unsigned) == 8);
  p5: assert final ($bits(some_logic_unsigned) == 8);
  p6: assert final ($bits(implicit_signed) == 8);
  p7: assert final ($bits(some_bits_signed) == 8);
  p8: assert final ($bits(some_logic_signed) == 8);

endmodule
