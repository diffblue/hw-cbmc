module main;

  function [31:0] logval;
    input [63:0] value;
    begin
      // the initial return value is a constant
      logval = logval + 32'h1;
    end
  endfunction

  // logval is an elaboration-time constant
  localparam VAL = logval(16);

endmodule
