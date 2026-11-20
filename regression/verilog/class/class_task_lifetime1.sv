class myClass;
  int x;

  automatic task set_x(input int value);
    x = value;
  endtask

  task automatic set_x2(input int value);
    x = value * 2;
  endtask

  task static set_x3(input int value);
    x = value * 3;
  endtask
endclass

module main;
  myClass c = null;
endmodule
