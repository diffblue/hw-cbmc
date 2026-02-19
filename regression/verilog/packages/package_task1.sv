package moo;

  int data;

  task foo;
    data = 123;
  endtask

endpackage

module main;

  initial begin
    // This does not parse with Icarus Verilog.
    moo::foo();
    assert(moo::data == 123);
  end

endmodule
