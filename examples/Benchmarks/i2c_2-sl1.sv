module i2cStrech(input clk, input rst, input scl_not_ena, output reg data_clk, output reg switch_range);
	localparam divider = 250;
	localparam CBITS = 10;
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
		if(2*divider <= cnt && cnt <= 3*divider - 1)
        	switch_range = 1;
      	else
        	switch_range = 0;
	end
    sl1: assert property (@(posedge clk) (always !rst) implies always (!stretch implies (!stretch s_until switch_range)));
    // ((G !rst -> G (!stretch -> !stretch U switch_range)))
endmodule
