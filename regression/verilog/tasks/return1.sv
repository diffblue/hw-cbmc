module main;

  int some_data;

  task some_task();
    some_data = 123;
    return;
  endtask

  initial begin : blk
    some_task();
    assert(some_data == 123);
  end

endmodule
