// Arrays of interface ports (IEEE 1800-2017 25.4), descending range
interface myInterface;
  int i;
endinterface

module sub(myInterface bus[3:1]);
  initial assert(bus[3].i == 30);
  initial assert(bus[2].i == 20);
  initial assert(bus[1].i == 10);
endmodule

module main;
  myInterface a(), b(), c();

  initial begin
    a.i = 30;
    b.i = 20;
    c.i = 10;
  end

  sub sub_inst('{a, b, c});
endmodule
