module main;

  // wildcard equality operator
  // 1800-2017 11.4.6
  property01: assert final ((10==?10)===1);
  property02: assert final ((10==?20)===0);
  property03: assert final ((10!=?20)===1);
  property04: assert final ((10==?20)===0);
  property05: assert final ((2'b00==?2'b0x)===1);
  property06: assert final ((2'b10==?2'b0x)===0);
  property07: assert final ((2'b00!=?2'b0x)===0);
  property08: assert final ((2'b10!=?2'b0x)===1);
  property09: assert final ((1'sb1==?2'b11)===0); // zero extension
  property10: assert final ((1'sb1==?2'sb11)===1); // sign extension

endmodule
