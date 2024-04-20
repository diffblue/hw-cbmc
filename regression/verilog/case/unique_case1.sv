module main(input x);

  always_comb // unique
    unique casex (x)
      0:;
      1:;
    endcase
    
  always_comb // not unique
    unique casex (x)
      0:;
      'b1?:;
    endcase
    
endmodule
