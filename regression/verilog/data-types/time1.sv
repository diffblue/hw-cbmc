module main;

  initial begin : some_block
    time some_time;
    some_time = 1;
    assert(some_time == 1);
    some_time++;
    assert(some_time == 2);
    assert($bits(some_time) == 64);
  end

endmodule
