module main(out, enable ,clk);
   parameter size = 16;
   parameter init_val = (1 << 12)+1;
   parameter rst_val = 1 << 10;
   //
   output [size:0] out;
   input           enable, clk;
   reg [size:0]    out;
   initial begin
      out = init_val;
   end
   always @(posedge clk) begin
      if (out == rst_val) begin
         out = 8'b0;
      end else if (enable) begin
         out = out + 1;
      end           
      // assert p1: !reset || (out == 0);
      // assert p2: !enable || (out != 0 || out == 0);
   end
    assert property ((out  >= init_val) || (out <= rst_val));  
    assert property (!((out > rst_val+60) && (out < init_val - 100)));
    assert property (out != init_val-1);
endmodule 
