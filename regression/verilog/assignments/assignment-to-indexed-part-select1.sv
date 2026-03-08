module main;

  // based on 1800 2017 11.5.1

  logic [31: 0] a_vect;

  always_comb begin
    a_vect[ 0 +: 8] = 8'hab;
    a_vect[15 -: 8] = 8'hcd;
    assert(a_vect[ 7 : 0] == 8'hab);
    assert(a_vect[15 : 8] == 8'hcd);
  end

  logic [0 :31] b_vect;

  always_comb begin
    b_vect[ 0 +: 8] = 8'hab;
    b_vect[15 -: 8] = 8'hcd;
    assert(b_vect[0 : 7] == 8'hab);
    assert(b_vect[8 :15] == 8'hcd);
  end

endmodule
