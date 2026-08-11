// Arrays of interface ports (IEEE 1800-2017 25.4)
interface myInterface;
  wire a;
  modport some_port(input a);
endinterface

// with a modport
module sub1(myInterface.some_port bus[0:3]);
endmodule

// without a modport
module sub2(myInterface bus[4]);
endmodule

// multiple dimensions
module sub3(myInterface bus[0:1][0:2]);
endmodule

module main;
endmodule
