module main;

  parameter type T1 = bit;
  localparam type T2 = bit [31:0];

  p1: assert property ($bits(T1) == 1);
  p2: assert property ($bits(T2) == 32);

endmodule
