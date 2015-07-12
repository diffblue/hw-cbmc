module main();

  assert property ($onehot('b0001000));
  assert property (!$onehot('b0101000));
  assert property (!$onehot('b00000));
  assert property ($onehot0('b00000));
  assert property ($onehot0('b000100));
  assert property (!$onehot0('b010100));

endmodule
