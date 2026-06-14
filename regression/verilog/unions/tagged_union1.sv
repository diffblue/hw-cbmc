module main;
  typedef union tagged {
    void Invalid;
    int Valid;
  } VInt;

  VInt v;

  initial v = tagged Invalid;

  VInt i;

  initial i = tagged Valid 123;

endmodule
