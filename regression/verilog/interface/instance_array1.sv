// An array of module instances, 1800-2017 23.3.2, where the module has
// an interface port. The same interface instance is connected to the
// port of every element of the array.
interface my_if;
  logic [3:0] v;
endinterface

module sub(my_if bus);
  p0: assert property (bus.v == 4'd5);
endmodule

module main;
  my_if i();
  assign i.v = 4'd5;

  sub s[0:1](.bus(i));
endmodule
