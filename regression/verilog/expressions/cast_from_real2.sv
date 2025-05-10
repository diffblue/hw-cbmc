module main;

  int a, b, c, d;

  // implicit casting as part of an assignment
  initial begin
    a = 0.0;
    assert(a == 0);
    b = 1.0;
    assert(b == 1);
    c = 0.5;
    assert(c == 1);
    d = -0.5;
    assert(d == -1);
  end

endmodule
