interface myInterface;
  wire a;
  modport some_port(input a);
endinterface

module sub(myInterface.some_port bus);
endmodule

module main;
endmodule
