module main;

   p0: assert property ($bits(byte) == 8);
   p1: assert property ($bits(shortint) == 16);
   p2: assert property ($bits(int) == 32);
   p3: assert property ($bits(longint) == 64);
   p4: assert property ($bits(integer) == 32);
   p5: assert property ($bits(time) == 64);

endmodule
