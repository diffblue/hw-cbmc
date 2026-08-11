// Arrays of interface ports (IEEE 1800-2017 25.4)
interface myInterface;
  int i;
endinterface

module sub(myInterface bus[0:1]);
  // The two elements are distinct interface instances.
  initial assert(bus[0].i == bus[1].i);
endmodule

module main;
  myInterface a(), b();

  initial begin
    a.i = 1;
    b.i = 2;
  end

  sub sub_inst('{a, b});
endmodule
