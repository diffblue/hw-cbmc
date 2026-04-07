module main;

  function [31:0] foo;
    // SystemVerilog allows multiple statements per body
    reg [31:0] x;
    x = 123;
    foo = x;
  endfunction;

  assert final (foo() == 123);

endmodule
