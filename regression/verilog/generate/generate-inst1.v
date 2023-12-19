module moduleA();
endmodule

module moduleB();
endmodule

module main();

  parameter cond = 1;

  generate
    if(cond)
      moduleA inst();
    else
      moduleB inst();
  endgenerate

endmodule // main
