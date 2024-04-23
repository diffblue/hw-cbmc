module main(input x);

  always_comb // unique
    unique if (x == 0)
      ;
    else if(x == 1)
      ;
    
  always_comb // not unique
    unique if (x == 0)
      ;
    else if(x&'b10 == 1)
      ;
    
endmodule
