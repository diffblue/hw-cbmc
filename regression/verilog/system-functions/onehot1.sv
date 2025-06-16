module main;

  pA0: assert final ($onehot(8'b00001000)==1);
  pA1: assert final ($onehot(8'b00001010)==0);
  pA2: assert final ($onehot(8'b11110111)==0);

  pB0: assert final ($onehot0(8'b00001000)==0);
  pB1: assert final ($onehot0(8'b00001010)==0);
  pB2: assert final ($onehot0(8'b11110111)==1);

  // $onehot and $onehot0 yield elaboration-time constants
  parameter Q1 = $onehot(3'b101);
  parameter P1 = $onehot0(3'b101);

endmodule
