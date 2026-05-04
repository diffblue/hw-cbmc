interface class ia;
  pure virtual function int a();
endclass

interface class ib;
  pure virtual function int b();
endclass

interface class ic extends ia, ib;
  pure virtual function int c();
endclass

module main;
endmodule
