package my_pkg;
  byte some_name, other_name;
endpackage

int some_name;

module main(input int other_name);
  import my_pkg::*;

  // This resolves to my_pkg::some_name, not $unit::some_name
  initial assert($bits(some_name) == 8);

  // This resolves to main.other_name, not my_pkg::other_name
  initial assert($bits(other_name) == 32);

endmodule
