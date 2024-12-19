module main();

  assert final ($onehot('b0001000));
  assert final (!$onehot('b0101000));
  assert final (!$onehot('b00000));
  assert final (!$onehot0(6'b00000));
  assert final (!$onehot0(6'b000100));
  assert final (!$onehot0(6'b010100));
  assert final ($onehot0(6'b111101));

endmodule
