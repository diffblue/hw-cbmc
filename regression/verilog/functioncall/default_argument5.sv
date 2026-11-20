module main(input [7:0] i);

  // We require default values to be elaboration-time constants.
  function automatic [7:0] f(input [7:0] a = i);
    f = a;
  endfunction

  p0: assert final (f() == i);

endmodule
