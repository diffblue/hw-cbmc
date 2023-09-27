module main(in, out);
    input [7:0]	in;
    output [8:0] out;
    reg [8:0] out;

    function [7:0] toLower;
    input [7:0]   in;
    begin: convToLower
      if(isUpper(in))
        toLower = in + 8'h20;
      else
        toLower=in;
    end
    endfunction

    function isUpper;
    input [7:0] in;
    begin: testIsUpper
	isUpper = ~in[5];
    end
    endfunction
    
    always @in begin
      out <= toLower(in);
    end

    always assert test1: !(in==65) || (out==97); // A -> a

endmodule
