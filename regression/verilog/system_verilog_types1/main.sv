module main;

  bit signed [2:0] abc;
  int signed       xyz;
  enum { A, B, C=99 }  enm;
   
  typedef struct { bit [7:0] A,B; } AB_t;
  AB_t AB[10]; 

endmodule
