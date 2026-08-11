// Arrays of interface ports (IEEE 1800-2017 25.4)
interface myInterface;
  int i;
endinterface

module leaf(myInterface bus[0:1]);
  initial assert(bus[0].i == 40);
  initial assert(bus[1].i == 50);
endmodule

module mid(myInterface bus[0:1]);
  // pass on the array of interface ports, given by its name
  leaf leaf_inst(bus);
endmodule

module main;
  myInterface a(), b();

  initial begin
    a.i = 40;
    b.i = 50;
  end

  mid mid_inst('{a, b});
endmodule
