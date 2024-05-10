module LCD #(localparam clk_freq = 25, localparam CBITS = 14) (input clk, input [6:0] in_data, input lcd_enable, input [9:0] lcd_bus, output reg e, output reg[7:0] lcd_data, output reg rw, output reg rs, output reg busy);
	reg [CBITS - 1:0] cnt;			// 0 to 500*clk_freg
	reg [1:0] state;

	always @(posedge clk) begin
		rw = 0;
		rs = 0;
		busy = 0;
		lcd_data = 0;
		e = 0;
		if(state == 0) begin
			busy = 1;
			if(cnt < 500*clk_freq)				// wait 500
				cnt = cnt + 1;
			else begin							// power-up completed
				cnt = 0;
				rs = 0;
				rw = 0;
				lcd_data = 8'b00110000;
				state = 1;
			end
		end
		if(state == 1) begin
			busy = 1;
			cnt = cnt + 1;
			if(cnt < (10*clk_freq))begin			//function set
				lcd_data = {4'b0011, in_data[6], in_data[5], 2'b00};
				e = 1;
			end
			else if(cnt < (60*clk_freq))begin		// wait 50
				lcd_data = 8'b00000000;
				e = 0;
			end
			else if(cnt < (70*clk_freq))begin		//display on/off control
				lcd_data = {5'b00001, in_data[4], in_data[3], in_data[2]};
				e = 1;
			end
			else if(cnt < (120*clk_freq))begin		// wait 50
				lcd_data = 8'b00000000;
				e = 0;
			end
			else if(cnt < (130*clk_freq))begin		// display clear
				lcd_data = 8'b00000001;
				e = 1;
			end
			else if(cnt < (330*clk_freq))begin		// wait 200
				lcd_data = 8'b00000000;
				e = 0;
			end
			else if(cnt < (340*clk_freq))begin		// entry mode set
				lcd_data = {6'b000001, in_data[1], in_data[0]};
				e = 1;
			end
			else if(cnt < (440*clk_freq))begin		// wait 100
				lcd_data = 8'b00000000;
				e = 0;
			end
			else begin								// initialization complete
				cnt = 0;
				busy = 0;
				state = 2;
			end
		end
		if(state == 2) begin
			if(lcd_enable == 1) begin
				busy = 1;
				rs = lcd_bus[9];
				rw = lcd_bus[8];
				lcd_data = lcd_bus[7:0];
				cnt = 0;
				state = 3;
			end
			else begin
				busy = 0;
				rs = 0;
				rw = 0;
				lcd_data = 8'b00000000;
				cnt = 0;
			end
		end
		if(state == 3) begin
			if(cnt < 50* clk_freq) begin 		// do not exit for 50
				if(cnt < clk_freq)
					e = 0;
				else if(cnt < 14*clk_freq)		// positive enable half-cycle
					e = 1;
				else if(cnt < 27*clk_freq)		// negative enable half-cycle
					e = 0;
				cnt = cnt + 1;
			end
			else begin
				cnt = 0;
				state = 2;
			end
		end
	end
	p1: assert property (@(posedge clk) s_eventually lcd_enable == 0 || state == 2);
	//F G (lcd_enable = T) -> G F (state[1] = T & state[0] = F)
endmodule
