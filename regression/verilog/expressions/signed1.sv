module main;

  wire signed [31:0] wire1 = -1;
  wire [31:0] wire2 = -1;
  
  p1: assert final (wire1==wire2);
  p2: assert final ((wire1 >>> 1)==-1);
  p3: assert final ((wire2 >>> 1)!=-1);
  p4: assert final ((wire1[31:0] >>> 1)!=-1); // part-selects are unsigned
  p5: assert final (($unsigned(wire1) >>> 1)!=-1);
  p6: assert final (($signed(wire2) >>> 1)==-1);
  p7: assert final ((-'d1 >>> 1)!=-1); // based numbers are unsigned
  p8: assert final ((-1 >>> 1)==-1);

endmodule
