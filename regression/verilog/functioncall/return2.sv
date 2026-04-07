function int some_int(bit some_input);
  int data;
  data = 456;

  if(some_input) begin
    data = 0;
    return 123;
  end

  return data;  
endfunction

module main;

  assert final (some_int(0) == 456);
  assert final (some_int(1) == 123);

endmodule
