module main(clk);
   parameter nelems = 5;
   parameter word_size = 10;
   input clk;
   reg [word_size:0] A[nelems-1:0];
   reg     finished;
   reg [word_size:0] Tmp;
   integer   i;
   reg       swap;
   reg      sorted;
   reg [word_size+6:0] sum,init_sum;
   initial begin
      A[0] = 102;
      A[1] = 100;
      A[2] = 5;
      A[3] = 200;
      A[4] = 300;
      // A[5] = 102;
      // A[6] = 100;
      // A[7] = 5;
      // A[8] = 200;
      // A[9] = 300;
      finished = 0;
      init_sum = 0;
      for (i = 0; i < nelems; i = i+1)
        begin
           init_sum = init_sum + A[i];
        end
      sum = init_sum;
      swap = 0;
      sorted = 0;
   end
   
   always @(posedge clk) begin
      if (!finished) begin
         swap = 0;
         for (i=nelems-2; i >= 0; i=i-1)
//           if (swap == 0)
             begin
                if (A[i+1] < A[i])
                  begin
                     Tmp = A[i];
                     A[i] = A[i+1];
                     A[i+1] = Tmp;                            
                     swap = 1;
                  end
             end
         if (swap == 0) finished = 1;  
      end // if (!finished)  
      sum = 0;
      for (i = 0; i < nelems; i=i+1)
        begin
           sum =  sum + A[i];
        end
      sorted = 1;
      for (i = 0; i < nelems-1; i=i+1)
        sorted = sorted & ((A[i] <A[i+1]) || (A[i] == A[i+1]));
   end //
   

   


   p0: assert property (sum == init_sum);
   p1: assert property (sum[7] == init_sum[7]);
   p2: assert property (!finished || sorted);
   p3:  assert property (!finished || (A[0] <= A[1]));
   p4:  assert property (!finished || (A[1] <= A[2]));
   p5:  assert property (!finished || (A[2] <= A[3]));
   p6:  assert property (!finished || (A[3] <= A[4]));
   p7:  assert property (!finished || (A[4] <= A[5]));
   p8:  assert property (!finished || (A[5] <= A[6]));
   p9:  assert property (!finished || (A[6] <= A[7]));
  
endmodule 
