module main(input a, b);

  // a property that is a sequence
  property lemma;
    a ##1 b
  endproperty

  assert property (lemma);

endmodule
