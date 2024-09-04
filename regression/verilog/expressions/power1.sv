module main;

  property01: assert final (2**0==1);
  property02: assert final (2**1==2);
  property03: assert final ((-2)**1==-2);
  property04: assert final (2**2==4);
  property05: assert final (2**-1==0);
  property06: assert final ($bits(3'd2**2)==3);
  property07: assert final (2**'bx===32'bx);
  property08: assert final ('bx**2===32'bx);

endmodule
