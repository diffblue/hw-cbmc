// Arrays of interface ports (IEEE 1800-2017 25.4), with a modport
interface myInterface;
  int i;
  initial i = 11;
  modport some_port(input i);
endinterface

module sub(myInterface.some_port bus[0:1]);
  initial assert(bus[1].i == 11);
endmodule

module main;
  myInterface a(), b();
  sub sub_inst('{a, b});
endmodule
