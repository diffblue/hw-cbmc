module main;

  function [7:0] identity(input [7:0] value);
    identity = value;
  endfunction

  // function ports are 'assignment-like contexts', 1800-2017 10.8,
  // and hence, the signed argument is sign extended
  assert final(identity(1'sb1) == 8'hff);

endmodule
