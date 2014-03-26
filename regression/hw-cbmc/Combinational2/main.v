module top(
  input [31:0] in,
  output reg signed [31:0] out);
        
  reg [5:0] shift;
          
  always @(*) begin
    shift = 0;
    out = in;
                        
    if (('hffff00 & in) == 0) begin
      out = out << 16;
      shift = shift + 16;
    end
  end

endmodule
