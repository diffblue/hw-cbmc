module main;

  typedef enum { A, B } AB_type;

  AB_type var1;
  AB_type var2;

  initial var2 = var1; // expected to typecheck

endmodule
