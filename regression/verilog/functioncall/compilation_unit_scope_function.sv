// a function in comilation unit scope
function integer my_func;
  my_func = 123;
endfunction

module main;
  localparam P = my_func();
  assert final (P == 123);
endmodule
