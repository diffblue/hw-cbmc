module M1(input [31:0] in1 = 1234, in2 = 4567);

  eq: assert final (in1 == in2);

endmodule

module main;
  // inputs not connected, should fail
  M1 m1();
  
  // in2 connected, should pass
  M1 m2(.in2(1234));
  
endmodule
