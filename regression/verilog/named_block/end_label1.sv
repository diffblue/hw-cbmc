module main;

  // End label after the "end" of a named block, IEEE 1800-2017 9.3.4.
  initial begin : blk
    int x;
    x = 3;
    p0: assert (x == 3);
  end : blk

endmodule
