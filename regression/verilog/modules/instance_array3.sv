// 1800-2017 23.3.3

module sub(output [1:0] o, input [1:0] i, input all);
  assign o = all ? i : ~i;
endmodule

module main;
  wire [7:0] o8, i8;
  wire one;
  assign i8 = 8'b1101_0010;
  assign one = 1;

  // The connection to i is split over the four instances;
  // the connection to all is replicated.
  sub s[3:0](.o(o8), .i(i8), .all(one));

  p1: assert property (o8 == 8'b1101_0010);
  p2: assert property (s[3].i == 2'b11);
  p3: assert property (s[0].i == 2'b10);
endmodule
