class myClass;
  int x;

  function int get_x();
    return x;
  endfunction

  virtual function int double_x();
    return x * 2;
  endfunction

  static function int zero();
    return 0;
  endfunction

  task set_x(input int value);
    x = value;
  endtask

  extern function void dump();
endclass

module main;
  myClass c = null;
endmodule
