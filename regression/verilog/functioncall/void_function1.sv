module main;

  int x;

  function void doit();
    x = 123;
  endfunction

  initial foo();

  assert final (x == 123);

endmodule
