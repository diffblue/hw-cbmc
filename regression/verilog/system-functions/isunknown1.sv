module main;

  p0: assert final ($isunknown(123)==0);
  p1: assert final ($isunknown('z)==1);
  p2: assert final ($isunknown('x)==1);
  p3: assert final ($isunknown('b01x0)==1);
  p4: assert final ($isunknown(3'bzzz)==1);

  // $isunknown yields an elaboration-time constant
  parameter Q1 = $isunknown(3'b10z);
  parameter P1 = $isunknown(3'b101);

endmodule
