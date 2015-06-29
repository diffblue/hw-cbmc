module main;

  wire signed [31:0] wire1 = -1;
  wire [31:0] wire2 = -1;
  
  always assert p1: wire1==wire2;
  always assert p2: (wire1 >>> 1)==-1;
  always assert p3: (wire2 >>> 1)!=-1;
  always assert p4: (wire1[31:0] >>> 1)!=-1; // part-selects are unsigned
  always assert p5: ($unsigned(wire1) >>> 1)!=-1;
  always assert p6: ($signed(wire2) >>> 1)==-1;
  always assert p7: (-'d1 >>> 1)!=-1; // based numbers are unsigned
  always assert p8: (-1 >>> 1)==-1;

endmodule
