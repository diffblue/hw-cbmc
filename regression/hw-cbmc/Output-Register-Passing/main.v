// This is an example of output register passing
// and output passing. Here, o1 is output register 
// and o2 is only output

module top(in1, in2);                       
  input [3:0] in1, in2;          
  wire [3:0] in1, in2;          
  wire [3:0] o1;                                                         
  wire [3:0] o2;   

  parameter [1:0] x = 2'b00;
  parameter [1:0] y = 2'b01;

  and1 A1 (in1, in2, o1, o2);             
                                
  /* A2 is another instance of      
     ports are referenced to the       
     declaration by name. */           
  and1 A2 (.c(o1),.d(o2),.a(o1),.b(in2)); 

endmodule                       
                                     
// MODULE DEFINITION              
module and1(a, b, c, d);              
  input [3:0] a, b;                 
  output [3:0] c;
  output [3:0] d;
  reg [3:0] c;                                

  always @(*) begin
   c = a & b;      
  end
  
  assign d = 1; 
endmodule   


