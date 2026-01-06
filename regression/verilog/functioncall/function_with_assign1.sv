function [31:0] some_function;
  bit [31:0] some_data;
  assign some_data = 123;
  some_function = some_data;
endfunction

module main;
  assert property (some_function() == 123);
endmodule
