module main;

  parameter Q = 5;

  function automatic [7:0] g(input [7:0] a = Q);
    g = a;
  endfunction

  initial begin : b
    // This does not affect the default value of g's argument,
    // which is evaluated in the scope of the declaration (1800-2017 13.5.3).
    reg [7:0] Q;
    Q = 1;
    assert(g() == 5);
  end

endmodule
