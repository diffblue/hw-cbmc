virtual class myBase;
  pure virtual function int area();
endclass : myBase

class myClass extends myBase;
  int width;

  virtual function int area();
    return width * width;
  endfunction
endclass : myClass

module main;
  myClass c = null;
endmodule
