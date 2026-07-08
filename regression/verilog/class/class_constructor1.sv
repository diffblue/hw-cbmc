class myClass;
  int x;

  function new(int initial_value);
    x = initial_value;
  endfunction : new
endclass

class emptyClass;
  function new;
  endfunction
endclass

module main;
  myClass c = null;
endmodule
