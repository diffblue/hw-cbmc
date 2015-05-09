module top(clk,rst,ser_in,done); 

  input clk,rst;
  input ser_in;
  output done;
  wire [7:0] ser_in;
  reg done;

  reg [7:0] s0_in; reg [7:0] s1_in; reg [7:0] s2_in;
  reg [9:0] xsum1_in; reg [9:0] xsum2_in;
  reg [7:0] xavg_out, xdiff_out;
  reg [7:0] xavg_next;
  reg [1:0] state;

  always @(posedge clk) begin: update
    if (rst) begin
      xavg_out <= 0;
      xdiff_out <= 0;
      state <= 2'b00;
    end else begin: normal
      if (state==2'b00) begin
        s0_in <= ser_in;
        state <= 2'b01;
      end
      else if (state==2'b01) begin
        s1_in <= ser_in;
        state <= 2'b10;
      end
      else if (state==2'b10) begin //state==10
        s2_in <= ser_in;
        xsum1_in <= s0_in + s1_in;
        state <= 2'b11;
      end
      else //state==11
      begin
        xsum2_in = ser_in + s2_in;
        xavg_next = (xsum1_in + xsum2_in)>>2;
        xavg_out <= xavg_next;
        if (xavg_next >= ser_in)
          xdiff_out <= xavg_next - ser_in;
        else xdiff_out <= ser_in - xavg_next;
        state <= 2'b00;
      end
    end
  end

  always @(*)
    done = (state==2'b00);

endmodule
