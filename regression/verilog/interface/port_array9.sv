// Arrays of interface ports (IEEE 1800-2017 25.4)
interface myInterface;
  int i;
endinterface

module sub(myInterface bus[0:1]);
  // out of range
  initial assert(bus[2].i == 0);
endmodule

module main;
  myInterface a(), b();
  sub sub_inst('{a, b});
endmodule
