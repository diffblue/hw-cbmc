module top(rst, clk);
input clk, rst;
reg [15:0] a;
reg [7:0] a1[3:0];
reg [7:0] a2[3:0];
reg [7:0] a3[7:0];
reg [7:0] a4[7:0];

genvar      i;
 generate
 for(i=0;i<2;i=i+1) begin : forblock
   always @ (posedge clk) begin
     if(a[i]) begin
       a1[2*i + 2 - 1 : 2*i] <= a2[2*i + 2 - 1: 2*i];
       a3[2*i+1 : 2*i] = a4[4*i+1 : 4*i];
     end 
   end
  end  
 endgenerate
endmodule




