module main;

  // recursive let instances are not allowed, 1800-2017 11.12
  let f(a) = f(a);
  p0: assert final (f(1) == 1);

endmodule
