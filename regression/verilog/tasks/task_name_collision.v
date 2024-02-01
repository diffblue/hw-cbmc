module main;

  reg [31:0] data;

  task some_task;
    data = 123;
  endtask

  task some_task;
    data = 456;
  endtask

endmodule
