module main(out1,out2,enable ,clk, reset);
   parameter ms_bit = 31;
   parameter thresh = 10000000;
//   parameter thresh2 = thresh1;
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
         if (sum1 >= thresh) sum1 = 0;
         else sum1 = sum1 + 1;
         if (sum2 == thresh) sum2 = 0;
         else sum2 = sum2 + 1;
   //   if (sum2 == thresh + 2000) sum2 = 134343;
      end              
   end
   // assign out1 = (sum1 != thresh2 + 1);
   // assign out2 = (sum2 != thresh2 + 1);
   p0: assert property (sum1 == sum2);
   p1: assert property ((sum1 == sum2) || (sum1 > thresh+100));
   // p1: assert property (sum1[0] == sum2[0]);
   // p2: assert property (sum1[1] == sum2[1]);
   // p3: assert property (sum1[2] == sum2[2]);
   // p4: assert property (sum1[3] == sum2[3]);
   // p5: assert property (sum1[4] == sum2[4]);
   // p6: assert property (sum1[5] == sum2[5]);
   // p7: assert property (sum1[6] == sum2[6]);
   // p8: assert property (sum1[7] == sum2[7]);
   // p9: assert property (sum1[ms_bit-1] == sum2[ms_bit-1]);
   // p10:assert property (sum1[ms_bit] == sum2[ms_bit]);
endmodule 
