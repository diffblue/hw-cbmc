module SEVEN(input clk, input rst, input [13:0] both7seg, output reg[6:0] segment, output reg sig);
	localparam freq = 17500;
	localparam CBITS = 15;

	reg [CBITS-1:0] cnt;
	reg digit_select;

	always @(posedge clk) begin
		if(rst == 1) begin
			cnt = 0;
			digit_select = 0;
			segment = 0;
		end
		if(cnt < freq) begin
			cnt = cnt + 1;
			sig = 0;
		end
		else begin
			sig = 1;
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

  // LTLSPEC G (Verilog.SEVEN.rst = FALSE) -> G  ( ((Verilog.SEVEN.digit_select = FALSE & X Verilog.SEVEN.digit_select = FALSE ) | (Verilog.SEVEN.digit_select = TRUE & X Verilog.SEVEN.digit_select = TRUE )) U X Verilog.SEVEN.sig = TRUE) 
  assert property (@(posedge clk) (always !rst) implies always ((digit_select iff s_nexttime digit_select) s_until s_nexttime sig));

endmodule
