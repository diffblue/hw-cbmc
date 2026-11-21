module main;

  typedef enum { A, B } ab_t;

  ab_t x, y;

  initial begin
    x = A;
    // The conditional operator with two operands of the same enum type
    // yields that enum type, and hence, can be assigned to an enum.
    y = x == A ? B : A;
    assert (y == B);
  end

endmodule
