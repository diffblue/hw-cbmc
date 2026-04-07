// P has no default value; allowed by 1800-2017 6.20.1
module my_module #(P);

endmodule

module main;

  // error: didn't give value for P
  my_module m1();

endmodule
