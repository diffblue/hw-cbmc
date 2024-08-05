module main;

  always assert ($countones('b10101)==3);

  // $countones yields an elaboration-time constant
  parameter P = 123;
  parameter Q = $countones(P);

endmodule
