module main;

  always assert property01: (10==10)===1;
  always assert property02: (10==20)===0;
  always assert property03: (10!=20)===1;
  always assert property04: (10==20)===0;
  always assert property05: ('bx==10)==='bx;
  always assert property06: ('bz==20)==='bx;
  always assert property07: ('bx!=10)==='bx;
  always assert property08: ('bz!=20)==='bx;
  always assert property09: ('sb1=='b11)===0; // zero extension
  always assert property10: ('sb1=='sb11)===1; // sign extension

endmodule
