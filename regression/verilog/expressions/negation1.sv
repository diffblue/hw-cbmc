module main;

  property01: assert final (!0===1);
  property02: assert final (!1===0);
  property03: assert final (!2===0);
  property04: assert final ($bits(!4'd1)==1);
  property05: assert final (!1'bx===1'bx);
  property06: assert final (!2'bxx===1'bx);
  property07: assert final (!1'bz===1'bx);

  // expression type contexts do not pass through !
  initial assert(!(1'b1 + 1'b1) == 1);

endmodule
