module main;

  always assert property01: (10===10)==1;
  always assert property02: (10===20)==0;
  always assert property03: (10!==10)==1;
  always assert property04: (10!==20)==0;
  always assert property05: ('bx==='bx)==1;
  always assert property06: ('bz==='bz)==1;
  always assert property07: ('bx==='bz)==0;
  always assert property08: ('bx==='b1)==0;
  always assert property09: ('bz==='b1)==0;
  always assert property10: ('b1==='b01)==1; // zero extension
  always assert property11: ('b1==='sb11)==0; // zero extension
  always assert property12: ('sb1==='sb11)==1; // sign extension

endmodule
