// Arrays of interface ports (IEEE 1800-2017 25.4), multiple dimensions
interface myInterface;
  int i;
  initial i = 7;
endinterface

module sub(myInterface bus[0:1][0:2]);
  initial assert(bus[0][2].i == 7);
  initial assert(bus[1][0].i == 7);
endmodule

module main;
  myInterface a(), b(), c(), d(), e(), f();
  sub sub_inst('{'{a, b, c}, '{d, e, f}});
endmodule
