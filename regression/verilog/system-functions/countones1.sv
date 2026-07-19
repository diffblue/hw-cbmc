module main;

  initial assert($countones(5'b00000)==0);
  initial assert($countones(5'b10101)==3);

  // $countones yields an elaboration-time constant.
  // Icarus Verilog does not support this.
  parameter P = 123;
  parameter Q = $countones(P);

endmodule
