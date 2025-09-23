module main(input[31:0] in1, in2, in3);

  // follows
  // http://www.asic-world.com/verilog/operators2.html

  // replication
  always assert repli_p1: {4{4'b1001}}      == 'b1001100110011001;
  always assert repli_p2: {4{4'b1001,1'bz}} == 'b1001z1001z1001z1001z;

endmodule
