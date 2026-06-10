module main;

  task some_task;
    inout [31:0] some_inout;
    assert(some_inout == 123);
    some_inout = 456; // overwrite x
    assert(some_inout == 456);
  endtask

  reg [31:0] x;

  initial begin
    x = 123;
    some_task(x);
    assert(x == 456);
  end

endmodule
