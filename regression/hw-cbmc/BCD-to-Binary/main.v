module top(clk_i, dat_bcd_i, dat_bin_o, dat_gray_o);
input clk_i;
input [4:0] dat_bcd_i;

output [3:0] dat_bin_o;
output [3:0] dat_gray_o;

reg [3:0] dat_bin_o;
reg [3:0] dat_gray_o;
reg [3:0] tens_digit;
reg [3:0] no_tens_digit;
reg tens_select;

always @(posedge clk_i)
begin
  tens_digit <= dat_bcd_i[3:0] + 4'b1010;
  no_tens_digit <= dat_bcd_i[3:0];
  tens_select <= dat_bcd_i[4];
end

always @(posedge clk_i)
begin
  if (tens_select)
    dat_bin_o <= tens_digit;
  else
    dat_bin_o <= no_tens_digit;
end

always @(posedge clk_i)
begin
  dat_gray_o <= {dat_bin_o[3], ^dat_bin_o[3:2], ^dat_bin_o[2:1], ^dat_bin_o[1:0]};
end

endmodule
