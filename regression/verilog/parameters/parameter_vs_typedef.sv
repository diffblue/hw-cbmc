typedef int some_identifier;

module main;
  parameter some_identifier = 123;
  assert final(some_identifier == 123);
endmodule
