module main;
  parameter some_identifier = 4'b01xz;
  initial assert($bits(some_identifier) == 4);
  initial assert(some_identifier === 4'b01xz);
endmodule
