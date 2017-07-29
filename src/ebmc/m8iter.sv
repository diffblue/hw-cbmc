module main(out1,out2,enable ,clk, reset);
   parameter ms_bit = 7;
   parameter thresh1 = 50;
   parameter thresh2 = thresh1 + 10;
   input             enable, clk, reset;
   output            out1,out2;
   reg [ms_bit:0]    sum1;
   reg [ms_bit:0]    sum2;
   integer           i;
   initial begin
      for (i=0; i <= ms_bit; i=i+1) begin
         sum1[i] = 'b0;
         sum2[i] = 'b0;
      end
   end
   always @(posedge clk) begin
      if (enable) begin
         if (sum1 >= thesh1) sum1 = 0;
         else sum1 = sum1 + 1;
         if (sum2 >= thresh2) sum2 = 0;
         else sum2 = sum2 + 1;
      end              
   end
   assign out1 = (sum1 != thresh2 + 1);
   assign out2 = (sum2 != thresh2 + 1);
   p0: assert property (out1 == out2);
   // assert property (sum1[0] == sum2[0]);
   // assert property (sum1[1] == sum2[1]);
   // assert property (sum1[2] == sum2[2]);
   // assert property (sum1[3] == sum2[3]);
   // assert property (sum1[4] == sum2[4]);
   // assert property (sum1[5] == sum2[5]);
   // assert property (sum1[6] == sum2[6]);
   // assert property (sum1[7] == sum2[7]);
endmodule 
