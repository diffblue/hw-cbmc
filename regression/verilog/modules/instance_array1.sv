// 1800-2017 23.3.3.5

module child(output o, input i[5]);
  assign o = i[0] ^ i[1] ^ i[2] ^ i[3] ^ i[4];
endmodule : child

module parent(output o[8][4],
              input i[8][4][5] );
   child c[8][4](o,i);
   p1: assert property (o[3][2] == (i[3][2][0] ^ i[3][2][1] ^ i[3][2][2] ^ i[3][2][3] ^ i[3][2][4]));
   p2: assert property (o[7][0] == (i[7][0][0] ^ i[7][0][1] ^ i[7][0][2] ^ i[7][0][3] ^ i[7][0][4]));
endmodule : parent
