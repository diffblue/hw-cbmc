module main;

  wire signed one_bit_signed = -1;

  assert final (one_bit_signed == -1);
  assert final ($bits(one_bit_signed) == 1);

  wire unsigned one_bit_unsigned = 1;

  assert final (one_bit_unsigned == 1);
  assert final ($bits(one_bit_unsigned) == 1);

endmodule
