module main;

  function [31:0] incme;
    input value;
    integer value;
    incme = value + 1;
  endfunction

  initial assert(incme(10) == 11);

endmodule
