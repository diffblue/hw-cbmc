module main;

  assert final ((4'b0001 &  4'b1001) === 4'b0001);
  assert final ((4'b1001 &  4'bx001) === 4'bx001);
  assert final ((4'b1001 &  4'bz001) === 4'bx001);
  assert final ((4'b0001 |  4'b1001) === 4'b1001);
  assert final ((4'b0001 |  4'bx001) === 4'bx001);
  assert final ((4'b0001 |  4'bz001) === 4'bx001);
  assert final ((4'b0001 ^  4'b1001) === 4'b1000);
  assert final ((4'b0001 ^  4'bx001) === 4'bx000);
  assert final ((4'b0001 ^  4'bz001) === 4'bx000);
  assert final ((4'b0001 ~^ 4'b1001) === 4'b0111);
  assert final ((4'b0001 ~^ 4'bx001) === 4'bx111);
  assert final ((4'b0001 ~^ 4'bz001) === 4'bx111);

endmodule
