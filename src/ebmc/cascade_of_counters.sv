module main(enable ,clk);
   parameter ms_bit = 10;
   parameter thresh1 = 200;
   parameter thresh2 = 200;
   //  parameter nbits = ms_bit + 1;
   input enable, clk;
   reg [ms_bit:0] out1;
   reg [ms_bit:0] out2;
   integer        i;
    initial begin
      for (i=0; i <= ms_bit; i=i+1) begin
         out1[i] = 'b0;
         out2[i] = 'b0;
      end
   end
   always @(posedge clk) begin
      if (enable) begin
         if (out1 == thresh1+1) out1 = 0;
         else out1 = out1 + 1;

         if (out1 == thresh1+1) out2 = out2 + 1;      
      end //
   end //
   
   P1: assert property (out1 <= thresh1);
   P2: assert property (out2 != thresh2);  
endmodule 
