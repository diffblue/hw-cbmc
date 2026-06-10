module main;

  task some_task;
    ref [31:0] some_ref;
    assert(some_ref == 123);
    some_ref = 456; // overwrite x
    assert(some_ref == 456);
  endtask

  reg [31:0] x;

  initial begin
    x = 123;
    some_task(x);
    assert(x == 456);
  end

endmodule
