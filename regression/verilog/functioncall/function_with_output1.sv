// we both return a value and have an output port
function [31:0] func(output [31:0] some_output);
  some_output = 1;
  return 2;
endfunction

module main;

  initial begin
    int a, b;
    a = func(b);
    assert(a == 2);
    assert(b == 1);
  end

endmodule
