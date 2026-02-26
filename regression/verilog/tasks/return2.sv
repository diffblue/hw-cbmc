module main;

  int some_data;

  task some_task();
    return;
    // should not fail
    a0: assert(0);
  endtask

  initial begin
    some_task();
    // should fail
    a1: assert(0);
  end

endmodule
