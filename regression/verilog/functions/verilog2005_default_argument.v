module main;

  // Default argument values are defined in 1800-2017 13.5.3.
  // Not in 1364-2005.
  function f(input a = 1);
    f = a;
  endfunction

  wire y = f();

endmodule
