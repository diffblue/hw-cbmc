module main;

  // IEEE 1800-2017 6.17
  event done;
  event empty = null;

  task trigger_done;
    -> done;
  endtask

  task wait_until_done;
    @ done;
  endtask

endmodule
