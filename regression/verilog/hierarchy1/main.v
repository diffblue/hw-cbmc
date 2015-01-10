module SUB(input in, output out);

  assign out=in;

endmodule

module main;
  wire xxx1, xxx2;

  SUB sub(xxx1, xxx2);
  
  always assert property1: xxx2==xxx1;
  
endmodule
