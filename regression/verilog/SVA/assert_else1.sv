module main(input clk);

  task some_task;
    $fatal("property failed");
  endtask;

  assert property (0) else some_task();

endmodule
