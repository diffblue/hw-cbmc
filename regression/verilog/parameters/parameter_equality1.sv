module main #(parameter N = 8) ();

  localparam N_LG2 = $clog2(N);
  localparam N_IS_POWER_OF_2 = (1 << N_LG2) == N;
  localparam N_W = N_IS_POWER_OF_2 ? N_LG2 + 1 : N_LG2;

  initial assert(N_LG2 == 3);
  initial assert(N_IS_POWER_OF_2 == 1);
  initial assert(N_W == 4);

endmodule
