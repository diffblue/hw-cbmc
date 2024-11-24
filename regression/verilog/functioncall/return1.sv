module main;

  function int some_int();
    return 123;
  endfunction

  assert final (some_int() == 123);

endmodule
