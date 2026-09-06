// 1800-2017 23.3.3

module sub(input i);
endmodule

module main;
  wire [5:0] w;

  sub s[3:0](w);

endmodule
