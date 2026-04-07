module main;

  function [31:0] my_greater(int a, int b);
    my_greater = a > b;
  endfunction

  initial assert(my_greater(2, 1));
  initial assert(my_greater(.a(2), .b(1)));
  initial assert(my_greater(2, .b(1)));
  initial assert(!my_greater(.a(1), .b(2)));
  initial assert(!my_greater(.b(2), .a(1)));

endmodule
