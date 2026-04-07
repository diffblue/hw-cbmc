// 1800-2017 23.3.3.5

module child(output o, input i[5]);
   //...
endmodule : child

module parent(output o[8][4],
              input i[8][4][5] );
   child c[8][4](o,i);
   //...
endmodule : parent
