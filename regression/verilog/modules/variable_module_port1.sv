module M(input var [7:0] in, output var [7:0] out);

  always @in
    out = in + 1;

endmodule

module main;
  wire [7:0] data0, data1;

  M m(data0, data1);

  wire [7:0] comp = data0 + 1;

  always assert final1: data1 == comp;

endmodule
