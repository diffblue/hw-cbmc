module main;

  wire [1:0] some_sig;
  typedef bit [1:0] some_typedef;

  always assert ($bits(some_sig)==2);
  always assert ($bits(some_typedef)==2);
  always assert ($bits(bit)==1);

  // $bits yields an elaboration-time constant
  parameter P = $bits(bit);

endmodule
