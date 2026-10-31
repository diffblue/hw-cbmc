// A parameter port of the top-level module that has no value.
module main #(int N);
  p0: assert final (N == 1);
endmodule
