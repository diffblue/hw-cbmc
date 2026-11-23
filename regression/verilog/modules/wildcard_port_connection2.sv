module sub(input [7:0] in, output [7:0] out);

  assign out = in;

endmodule

module main(input [7:0] in, output [7:0] out);

  // 1800-2017 23.3.2.4: .* connects each port of sub to the
  // signal of the same name in main.
  sub dut(.*);

  always_comb assert (out == in);

endmodule
