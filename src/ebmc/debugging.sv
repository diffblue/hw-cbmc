module main(out, enable ,clk,req1,req2);
   parameter ms_bit = 16;
   parameter rst_val = 1 << 12;
   parameter dng_val = rst_val + 1;
   //
   output [ms_bit:0] out;
   input           enable, clk,req1,req2;
   reg [ms_bit:0]    out;
   wire              w;
   initial begin
      out = 0;
   end
   always @(posedge clk) begin
         if (enable) begin           
         out = out + 1;
         if ((out == rst_val) && (req1 && req2))
           out = 0;
      end           
   end
    assign w = req1 && req2;
    assert property (out < dng_val);
    assert property (w == 1);

endmodule 
