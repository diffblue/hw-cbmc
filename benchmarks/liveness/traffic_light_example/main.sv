module main (reset, clk, time_left);
input reset, clk;
output [7:0] time_left;

parameter RED_LIGHT    = 0;
parameter GREEN_LIGHT  = 1;
parameter YELLOW_LIGHT = 2;

wire [5:0] RED_count;
wire [5:0] GREEN_count;
wire [2:0] YELLOW_count;
reg  [1:0] Light_Sign;
reg  [7:0] Counter;

assign RED_count    = 6'h3F;
assign GREEN_count  = 6'h3F;
assign YELLOW_count = 3'h3F;


assign time_left = Counter;

initial begin
 Counter = 0;
 Light_Sign = 0;
end

always @(posedge clk) begin // or negedge reset) begin
   if (reset) begin
      Light_Sign <= RED_LIGHT;
      Counter <= 8'd0;
   end
   else begin
      case (Light_Sign)
         RED_LIGHT :
            Light_Sign <= (Counter == 8'd0) ? GREEN_LIGHT : RED_LIGHT;
         GREEN_LIGHT : 
            Light_Sign <= (Counter == 8'd0) ? YELLOW_LIGHT : GREEN_LIGHT;
         YELLOW_LIGHT : 
            Light_Sign <= (Counter == 8'd0) ? RED_LIGHT : YELLOW_LIGHT;
      endcase
      case (Light_Sign)
         RED_LIGHT :
            Counter <= (Counter == 8'd0) ? GREEN_count : Counter - 8'd1;
         GREEN_LIGHT : 
            Counter <= (Counter == 8'd0) ? YELLOW_count : Counter - 8'd1;
         YELLOW_LIGHT : 
            Counter <= (Counter == 8'd0) ? RED_count : Counter - 8'd1;
      endcase
   end
end
   //assume property (reset == 0);
   assert property (time_left != 8'd255);
   // this bug is manifested only after 41 iterations
   //assert property3: (Light_Sign != 2'd2);
   //assert property (Light_Sign != 2'd3);
endmodule

