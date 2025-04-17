module Thermocouple(input clk, input rst, input spi_not_busy, input [31:0] spi_rx_data, output reg [13:0] tc_temp_data, output reg [11:0] junction_temp_data, output reg [3:0] fault_bits);
	localparam clk_freq = 200;
	localparam CBITS = 10;			// 2^CBITS > clk_freq*3
	reg spi_ena;
	reg [1:0] state;
	reg [CBITS-1:0] cnt;
	always @(posedge clk)
		if(rst == 1) begin
			spi_ena = 0;
			tc_temp_data = 0;
			junction_temp_data = 0;
			fault_bits = 0;
			state = 0;
			cnt = 0;
		end
		else if(state == 0) begin
			if(cnt < clk_freq * 3)
				cnt = cnt + 1;
			else begin
				cnt = 0;
				state = 1;
			end
		end
		else if(state == 1) begin
			if(spi_not_busy == 1)
				spi_ena = 1;
			else begin
				spi_ena = 0;
				state = 2;
			end
		end
		else if(state == 2) begin
			tc_temp_data = spi_rx_data [31:18];
			junction_temp_data = spi_rx_data [15:4];
			fault_bits = {spi_rx_data[16], spi_rx_data[2:0]};
			if(cnt < clk_freq * 1)
				cnt = cnt + 1;
			else begin
				cnt = 0;
				state = 1;
			end
		end
		else
			state = 1;
    sl1: assert property (@(posedge clk) (always !rst) implies always (state==2 implies (state==2 s_until state==1)));
    // ((G !rst -> G (s2 -> s2 U s1)))
endmodule
