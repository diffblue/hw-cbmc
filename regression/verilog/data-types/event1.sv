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

  p0: assert final (empty == null);
  p1: assert final ($typename(event) == "event");

endmodule
