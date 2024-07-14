module main;

   p0: assert final ($bits(byte) == 8);
   p1: assert final ($bits(shortint) == 16);
   p2: assert final ($bits(int) == 32);
   p3: assert final ($bits(longint) == 64);
   p4: assert final ($bits(integer) == 32);
   p5: assert final ($bits(time) == 64);

endmodule
