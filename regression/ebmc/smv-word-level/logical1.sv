module main(input a, input b);

  wire w_land = a && b;
  wire w_lor = a || b;
  wire w_lnot = !a;

endmodule
