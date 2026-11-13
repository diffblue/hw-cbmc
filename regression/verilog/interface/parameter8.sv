// Interfaces with a type parameter bound to interface ports, with the
// default and with an override.
interface tif #(parameter type T = logic [7:0]);
  T a;
endinterface

module tu #(parameter W = 8) (tif s);
  p0: assert property ($bits(s.a) == W);
endmodule

module main;
  tif i1();
  tif #(.T(logic [3:0])) i2();
  tu u1(.s(i1));
  tu #(.W(4)) u2(.s(i2));
endmodule
