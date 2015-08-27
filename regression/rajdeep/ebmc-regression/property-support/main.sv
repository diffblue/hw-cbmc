module top(input wire rst, input wire clk);
  reg [7:0] x,y;
  reg flag;
  reg [1:0] state;
  reg [1:0] count;
  reg live;
  always @(posedge clk) begin
  if(rst) begin
       x = 8'h00;
       y = 8'h00;
       flag = 1'b0;
       state = 0;
       count = 0;
       live = 0;
  end
  else begin
    case(state) 
     0: begin
         y = y + 2;
         state = 1;
        end        
     1: begin
         if(y == 8'h12) begin
          flag = 1'b1;
          count = count + 1; 
          if(count == 3)
           state = 2;
          else state = 0;
         end 
         else begin
          flag = 1'b0;
          state = 0;
         end
        end 
     2: begin live <= 1; state = 3; end 
     3: begin live <= 0; state = 3; end
   endcase
  end 
 end

 // ************** Specification **************
 
 // property: F(live==1), weak eventual 
 P0: assert property (@(posedge clk) (rst == 0 && live == 0 |-> ##[0:$] live == 1));
 
 // property: GF(live==1), strong eventual 
 P1: assert property (@(posedge clk) (rst == 0 && live == 0 |-> strong(##[0:$] live == 1)); //ebmc doesnot support this

 // property: GF(flag==1), strong eventual
 property GF1;
  always (s_eventually (flag==1));
 endproperty
 P2: assert property(GF1);

 // property: GF(live==1), strong eventual 
 property GF2;
  always (s_eventually (live==1));
 endproperty
 P3: assert property(GF2);
 
endmodule
