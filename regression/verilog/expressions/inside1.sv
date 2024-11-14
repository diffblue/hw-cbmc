module main;

  assert final (2 inside {1, 2, 3});
  assert final (2 inside {3'b0?0});
  assert final (!(2 inside {3'b0?1}));
  assert final (2 inside {[1:3], [6:8]});
  assert final (!(4 inside {[1:3], [6:8]}));
  assert final ((1&&1) inside {1, 2, 3});

endmodule
