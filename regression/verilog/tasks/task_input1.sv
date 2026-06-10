module main;

  task some_task;
    input [31:0] some_input;
    assert(some_input == 123);
    some_input = 456; // won't overwrite x
    assert(some_input == 456);
  endtask

  reg [31:0] x;

  initial begin
    x = 123;
    some_task(x);
    assert(x == 123);
  end

endmodule
