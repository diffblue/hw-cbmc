module main(input clk);

  function negate;
  input in;
  begin
      negate = ~in;
  end
  endfunction

  // same function used twice

  wire my_wire0 = negate(0);
  wire my_wire1 = negate(1);

  always assert p0: (my_wire0 == 1);
  always assert p1: (my_wire1 == 0);

endmodule
