// Arrays of interface ports (IEEE 1800-2017 25.4)
interface myInterface;
  int i;
endinterface

module sub(myInterface bus[0:2]);
endmodule

module main;
  myInterface a(), b();
  // one interface instance short
  sub sub_inst('{a, b});
endmodule
