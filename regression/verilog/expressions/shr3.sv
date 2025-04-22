module main;

  assert final (3'b101 >> 1 === 3'b010);
  assert final ('b101 >> 1 === 'b10);
  assert final ('b1x0 >> 1 === 'b1x);
  assert final (3'b101 >> 'bx === 3'bxxx);

  assert final (3'b101 >>> 1 === 3'b010);
  assert final ('b101 >>> 1 === 'b10);
  assert final ('b1x0 >>> 1 === 'b1x);
  assert final (3'b101 >>> 'bx === 3'bxxx);

endmodule
