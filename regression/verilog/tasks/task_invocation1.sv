module top(output reg [31:0] y);

  task my_task;
    y=123;
  endtask

  // the parentheses are optional
  always_comb my_task;

  assert final (y==123);

endmodule
