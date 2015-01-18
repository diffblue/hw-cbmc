module top(clk,rst,ser_in,done); 

input clk,rst;
input ser_in;
output done;
wire [7:0] ser_in;
reg done;

reg [9:0] xsum_in;
reg [7:0] xavg_out, xdiff_out;
reg [7:0] xavg_next;
reg [1:0] state;
reg [0:0] once;

always @(posedge clk) begin: update
  if (rst) begin
     xavg_out <= 0;
     xdiff_out <= 0;
     state <= 2'b00;
  end else begin: normal
      if (state==2'b00) begin
        xsum_in <= ser_in;
        state <= 2'b01;
        once <= 1'b1;
        end
      else if (state==2'b01) begin
        xsum_in <= xsum_in + ser_in;
        once <= 1'b0;
        if (once) state <= 2'b01; else state <= 2'b10;
        end
      else //state==10
      begin
        xavg_next = (xsum_in + ser_in)>>2;
        xavg_out <= xavg_next;
        if (xavg_next >= ser_in)
            xdiff_out <= xavg_next - ser_in;
        else xdiff_out <= ser_in - xavg_next;
        state <= 2'b00;
       end
    end
  end
  
  always @(*) begin
  done = (state==2'b00);
  end

endmodule
