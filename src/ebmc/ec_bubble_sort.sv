module main(clk);
   parameter nelems = 7;
   parameter word_size = 10;
   input clk;
   reg [word_size:0] A1[nelems-1:0];
   reg [word_size:0] A2[nelems-1:0];
   reg     finished1,finished2;
   reg     equiv;
   reg [word_size:0] Tmp1,Tmp2;
   integer   i;
   reg       swap1,swap2;
   initial 
     begin
        A1[0] = 102;
        A1[1] = 100;
        A1[2] = 5;
        A1[3] = 200;
        A1[4] = 300;
        A1[5] = 102;
        A1[6] = 100;
        // A1[7] = 5;
        // A1[8] = 200;
        // A1[9] = 300;
        finished1 = 0;
        finished2 = 0;
        equiv = 0;
        swap1 = 0;
        swap2 = 0;
        for (i=0; i < nelems;i=i+1)
          A2[i] = A1[i];

     end // initial begin
 //
// direct sorting
   always @(posedge clk) begin
      if (!finished1) begin
         swap1 = 0;
         for (i=0; i < nelems-1; i=i+1)
             begin
                if (A1[i] > A1[i+1])
                  begin
                     Tmp1 = A1[i];
                     A1[i] = A1[i+1];
                     A1[i+1] = Tmp1;                            
                     swap1 = 1;
                  end
             end
         if (swap1 == 0) finished1 = 1;  
      end // if (!finished)  
   end //

//
// reverse sorting
   always @(posedge clk) begin
      if (!finished2) begin
         swap2 = 0;
         for (i=nelems-2; i >=0 ; i=i-1)
             begin
                if (A2[i] > A2[i+1])
                  begin
                     Tmp2 = A2[i];
                     A2[i] = A2[i+1];
                     A2[i+1] = Tmp2;                            
                     swap2 = 1;
                  end
             end
         if (swap2 == 0) finished2 = 1;  
      end // if (!finished)  
   end 

   always @(posedge clk) begin
      // if(finished1 && finished2)
      //   begin
      equiv = 1;
      for (i = 0; i < nelems-1; i=i+1)
        equiv = equiv && (A1[i] == A2[i]);
      //  end
   end
   
   p0:  assert property (!finished1 || !finished2 || equiv);
   p1:  assert property (!finished1 || !finished2 || (A1[0] == A2[0]));
   //p1:  assert property (!finished1 || (A1[0] < A1[1]) || (A1[0] == A1[1]));
   p2:  assert property (!finished1 || !finished2 || (A1[1] == A2[1]));
   p3:  assert property (!finished1 || !finished2 || (A1[2] == A2[2]));
   p4:  assert property (!finished1 || !finished2 || (A1[3] == A2[3]));
   p5:  assert property (!finished1 || !finished2 || (A1[4] == A2[4]));
  
endmodule 
