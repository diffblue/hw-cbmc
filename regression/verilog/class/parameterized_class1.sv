class stack #(type T = int, int DEPTH = 8);
  T mem[DEPTH];

  function T top();
    return mem[0];
  endfunction
endclass

module main;
  stack s = null;
endmodule
