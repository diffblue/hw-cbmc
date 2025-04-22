module main;

  assert final (3'b101 << 1 === 3'b010);
  assert final ('b101 << 1 === 'b1010);
  assert final ('b10x << 1 === 'b10x0);
  assert final (3'b101 << 'bx === 3'bxxx);

  assert final (3'b101 <<< 1 === 3'b010);
  assert final ('b101 <<< 1 === 'b1010);
  assert final ('b10x <<< 1 === 'b10x0);
  assert final (3'b101 <<< 'bx === 3'bxxx);

endmodule
