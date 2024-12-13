module main(input i);

  wire x;

  not (x, i);

  assert final (x == !i);

endmodule
