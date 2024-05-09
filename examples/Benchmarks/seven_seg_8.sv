module SEVEN #(localparam freq = 10000, localparam CBITS = 14) (input clk, input rst, input [13:0] both7seg, output reg[6:0] segment);
	reg [CBITS-1:0] cnt;
	reg digit_select;

	always @(posedge clk) begin
		if(rst == 1) begin
			cnt = 0;
			digit_select = 0;
			segment = 0;
		end
		if(cnt < freq)
			cnt = cnt + 1;
		else begin
			cnt = 0;
			if(digit_select == 0) begin
				digit_select = 1;
				segment = both7seg[13:7];
			end
			else begin
				digit_select = 0;
				segment = both7seg[6:0];
			end
		end
	end
	p1: assert property  (@(posedge clk) ((always s_eventually rst == 1 ) or (always s_eventually digit_select == 1)));
	p2: assert property  (@(posedge clk) ((always s_eventually rst == 1 ) or (always s_eventually digit_select == 0)));
	//F G (rst = FALSE) -> G F (digit_select = TRUE)
	//F G (rst = FALSE) -> G F (digit_select = FALSE)
endmodule




