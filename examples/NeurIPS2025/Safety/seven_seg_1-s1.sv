module SEVEN(input clk, input rst, input [13:0] both7seg, output reg[6:0] segment, output reg sig);
	localparam freq = 250;
	localparam CBITS = 8;

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

  // LTLSPEC X G ((Verilog.SEVEN.sig = FALSE & X Verilog.SEVEN.sig = FALSE & Verilog.SEVEN.rst = FALSE) -> ( (Verilog.SEVEN.digit_select = TRUE & X Verilog.SEVEN.digit_select = TRUE) | (Verilog.SEVEN.digit_select = FALSE & X Verilog.SEVEN.digit_select = FALSE) ) )
  assert property (@(posedge clk) (!sig and !rst and s_nexttime !sig) implies (digit_select iff s_nexttime digit_select));

endmodule
