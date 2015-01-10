module M1(input in, inout [7:0] data);

  assign data = in ? 'bzzzzzzzz : 200 ;
  
  always @(in, data)
    if(in) assert(data==100);

endmodule

module main;
  wire [7:0] data0, data1;
  
  M1 m1(0, data0);
  M1 m2(1, data1);

  assign data1 = 100 ;
  
  always assert property1: data0 == 200;
  
endmodule
