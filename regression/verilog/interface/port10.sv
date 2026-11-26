// An interface variable with an initial value in the interface and one
// assigned through an interface port. The initial procedures run in an
// unspecified order (1800-2017 9.2.1), and the variable holds one of the
// values afterwards.
interface data_if;
  logic [3:0] value;
  initial value = 1;
endinterface

module writer(data_if bus);
  initial bus.value = 2;
endmodule

module main(input [3:0] x);
  data_if shared();
  writer w(shared);

  p0: assert final (shared.value == 1 || shared.value == 2);

  // x is not constrained
  p1: assert final (x == 0);
endmodule
