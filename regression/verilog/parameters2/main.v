module test(in1, in2);                       

  parameter P = 4;
  parameter Q = 5;
  input [3:0] in1, in2;          
  wire [3:0] in1, in2;          
  wire [3:0] o1;                                                         
  wire [3:0] o2;   
  wire [3:0] tmp = P;
 
  my_m #( .Ptop(P), .Qtop(Q) ) t1(in1, in2, o1, o2); 
 
  assert property1: (tmp == 4); // successful

endmodule                       
                                     
module my_m(a, b, c, d);

  parameter Ptop = 8; // this should be redefined with 4
  parameter Qtop = 9; // this should be redefined with 5
  input [3:0] a, b;                 
 
  output [Ptop-1:0] c;
  output [Ptop-1:0] d;

  wire [3:0] tmp1 = Ptop; // tmp1 should be 4 now  

endmodule
