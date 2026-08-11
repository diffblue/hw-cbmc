// Arrays of interface ports (IEEE 1800-2017 25.4)
interface myInterface;
  int i;
  initial i = 123;
endinterface

module sub(myInterface bus[0:1]);
  initial assert(bus[0].i == 123);
  initial assert(bus[1].i == 123);
endmodule

module main;
  myInterface a0(), a1();
  sub sub_inst('{a0, a1});
endmodule
