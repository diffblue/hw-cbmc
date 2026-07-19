module main;

  initial assert($typename(shortint)=="shortint");
  initial assert($typename(int)=="int");
  initial assert($typename(longint)=="longint");
  initial assert($typename(byte)=="byte");
  initial assert($typename(time)=="time");

endmodule
