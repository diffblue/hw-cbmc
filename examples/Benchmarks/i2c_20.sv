module i2cStrech #(localparam divider = 70000, localparam CBITS = 19) (input clk, input rst, input scl_not_ena, output reg data_clk);
	reg [CBITS - 1:0] cnt;	//0 to 4*divider
	reg scl_clk;
	reg stretch;
	always @(posedge clk) begin
		if(rst == 1) begin
			stretch = 0;
			cnt = 0;
		end
		if(cnt >= divider*4 - 1)
			cnt = 0;
		else if(stretch == 0)
			cnt = cnt + 1;

		if( cnt <= divider - 1) begin
			scl_clk = 0;
			data_clk = 0;
		end
		else if( divider <= cnt && cnt <= 2*divider - 1) begin
			scl_clk = 0;
			data_clk = 1;
		end
		else if( 2*divider <= cnt && cnt <= 3*divider - 1) begin
			if(scl_clk == 0 & scl_not_ena == 0)
				stretch = 1;
			else
				stretch = 0;
			scl_clk = 1;
			data_clk = 1;
		end
		else begin
			scl_clk = 1;
			data_clk = 0;
		end
	end
	p1: assert property  ((always s_eventually (rst == 1 or scl_not_ena == 1)) or (always s_eventually sig == 1)) ;
	//F G (rst = F & scl_not_ena = F) -> G F (mode = T)
endmodule