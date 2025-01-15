module main;

  assert final (~0 === 'hffff_ffff);
  assert final (~1 === 'hffff_fffe);
  assert final (~(-('sd1)) === 0);
  assert final (~3'b101 === 3'b010);
  assert final (~3'bxxx === 3'bxxx);
  assert final (~3'bzzz === 3'bxxx);
  assert final (~3'b10x === 3'b01x);
  assert final (~3'b10z === 3'b01x);

endmodule
