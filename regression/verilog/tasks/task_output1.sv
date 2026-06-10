module main;

  task some_task;
    output [31:0] some_output;
    assert(some_output == 123); // default initialized, fails
    some_output = 456; // overwrite x
    assert(some_output == 456);
  endtask

  reg [31:0] x;

  initial begin
    x = 123;
    some_task(x);
    assert(x == 456);
  end

endmodule
