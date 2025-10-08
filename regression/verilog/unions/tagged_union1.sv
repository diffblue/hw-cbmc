module main;
  typedef union tagged {
    void Invalid;
    int Valid;
  } VInt;

  VInt v;

  initial v = tagged Invalid;

endmodule
