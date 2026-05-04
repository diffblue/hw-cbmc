interface class myInterface;
  pure virtual function int get();
endclass

interface class myOtherInterface;
  pure virtual function int put(int value);
endclass

class myClass implements myInterface, myOtherInterface;
  int x;

  virtual function int get();
    return x;
  endfunction

  virtual function int put(int value);
    x = value;
    return x;
  endfunction
endclass

module main;
  myClass c = null;
endmodule
