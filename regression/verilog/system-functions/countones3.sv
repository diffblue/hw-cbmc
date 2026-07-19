module main;

  initial assert($countones('x)==0);
  initial assert($countones('z)==0);
  initial assert($countones(5'b10x01)==2);
  initial assert($countones(5'b10z01)==2);

endmodule
