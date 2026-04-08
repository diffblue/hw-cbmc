typedef int some_name;

module main;

  typedef byte some_name;

  initial assert($bits(some_name) == 8);
  initial assert($bits($unit::some_name) == 32);

endmodule
