// a task in comilation unit scope
task my_task(output int o);
  o = 123;
endtask

module main;
  initial begin
    int data;
    my_task(data);
    assert(data == 123);
  end
endmodule
