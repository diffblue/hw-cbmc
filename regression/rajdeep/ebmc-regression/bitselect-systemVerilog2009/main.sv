module top(clk,rst);

input clk, rst;
reg [15:0] a[15:0];
reg [7:0] a1[3:0];
reg [7:0] a2[3:0];
reg [7:0] a3[7:0];
reg [7:0] a4[7:0];
wire [7:0] a5[7:0];
wire [7:0] a6;

 genvar      i;
 generate
 for(i=0;i<2;i=i+1) begin : alwaysblock
   always @ (posedge clk) begin
     if(a[(3*i)+1] >= a[(4*i)]) begin
       a1[2*i +: 2] <= a2[2*i +: 2];   // Semantic meaning: a1[2*i + 2 - 1 : 2*i] <= a2[2*i + 2 - 1: 2*i]
       a3[2*i+1 -: 8]  <= a4[4*i+1 -: 8]; // semantic meaning: a3[2*i+1 : 2*i] = a4[4*i+1 : 4*i]
     end
   end
 end
 endgenerate


genvar j;
 generate
 for(j=0;j<2;j=j+1) begin : contassign
    assign a5[j] = {a1[j] | a2[j]} & a6[2*j+1 -: 8]; // semantic meaning: a5[j] = a6[2*j+1 + 8-1 : 2*j+1] & {a1[j] | a2[j]}
 end
 endgenerate

endmodule
