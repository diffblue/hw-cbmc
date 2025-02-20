module main;

  typedef struct {int a, b;} S;
  var S x = '{b:1, a:0};

  assert final (x.a == 0);
  assert final (x.b == 1);

endmodule
