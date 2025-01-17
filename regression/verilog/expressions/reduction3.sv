module main;

  assert final ( & 4'b1001 === 'b0);
  assert final ( & 4'bx111 === 'bx);
  assert final ( & 4'bz111 === 'bx);
  assert final (~& 4'b1001 === 'b1);
  assert final (~& 4'bx001 === 'b1);
  assert final (~& 4'bz001 === 'b1);
  assert final ( | 4'b1001 === 'b1);
  assert final ( | 4'bx000 === 'bx);
  assert final ( | 4'bz000 === 'bx);
  assert final (~| 4'b1001 === 'b0);
  assert final (~| 4'bx001 === 'b0);
  assert final (~| 4'bz001 === 'b0);
  assert final ( ^ 4'b1001 === 'b0);
  assert final ( ^ 4'bx001 === 'bx);
  assert final ( ^ 4'bz001 === 'bx);
  assert final (~^ 4'b1001 === 'b1);
  assert final (~^ 4'bx001 === 'bx);
  assert final (~^ 4'bz001 === 'bx);

endmodule
