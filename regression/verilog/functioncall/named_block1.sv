module main;

  function [31:0] foo;
  begin : block_name
    reg [31:0] x;
    x = 123;
    foo = x;
  end
  endfunction;

  assert final (foo() == 123);

endmodule
