class base;
  int x;

  function new(int v);
    x = v;
  endfunction
endclass

class derived extends base(42);
endclass

module main;
  derived d = null;
endmodule
