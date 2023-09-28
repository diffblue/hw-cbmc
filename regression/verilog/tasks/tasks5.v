module top(input in);

  reg out1, out2;

  always @(in) my_task(in, out1);
  always @(in) my_task(in, out2);

  task my_task(input x, output y);
    y=x;
  endtask

endmodule
