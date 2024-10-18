module main(input [31:0] a);

  a1: assume final (10<=a && a<=100);

  p1: assert final (a!=200);

  // would fail
  p2: assert final (a!=20);

endmodule 
