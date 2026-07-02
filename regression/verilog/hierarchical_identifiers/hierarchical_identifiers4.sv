module sub;
  reg [7:0] value;
endmodule

module main;
  sub s();
  initial s.value = 8'hAB;
  p0: assert property (s.value == 8'hAB);
endmodule
